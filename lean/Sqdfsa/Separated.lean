import Sqdfsa.FSA

/-!
# Separated finite-state automata (thesis §3.1)

A partition `{X, Q_1, …, Q_k}` of `Q` is given by `part : Q → Option ι`
(`none` ↦ `X`, `some i` ↦ `Q_i`). The thesis additionally requires every block to be nonempty
and `k > 1`; none of the results below need this, so it is recorded separately in
`IsKSeparated` and the theorems are stated for arbitrary separators.
-/

namespace Sqdfsa

variable {α Q ι : Type*}

section Partition

variable (part : Q → Option ι)

/-- The separator `X`. -/
def sepX : Set Q := {q | part q = none}

/-- The component `𝒞(Q_i) = Q_i ∪ X`. -/
def comp (i : ι) : Set Q := {q | part q = none ∨ part q = some i}

variable {part}

theorem sepX_subset_comp (i : ι) : sepX part ⊆ comp part i := fun _ h => Or.inl h

/-- Every state lies in some component. -/
theorem exists_mem_comp [Nonempty ι] (q : Q) : ∃ i, q ∈ comp part i := by
  rcases h : part q with _ | i
  · exact ⟨Classical.arbitrary ι, Or.inl h⟩
  · exact ⟨i, Or.inr h⟩

end Partition

namespace FSA

variable (A : FSA α Q) (part : Q → Option ι)

/-- `X` is a separator in `A`: no transition joins two different blocks. -/
def IsSeparator : Prop :=
  ∀ q a q' i j, (q, a, q') ∈ A.delta → part q = some i → part q' = some j → i = j

/-- The full thesis definition of a `k`-separated automaton (nonempty blocks, `k > 1`). -/
def IsKSeparated [Fintype ι] (k : ℕ) : Prop :=
  A.IsSeparator part ∧ Fintype.card ι = k ∧ 1 < k ∧ (sepX part).Nonempty ∧
    ∀ i, {q | part q = some i}.Nonempty

variable {A part}

/-- Proposition (§3.1): a separator in the graph `𝒢_A` is a separator in `A`. -/
theorem isSeparator_of_graph (h : IsGraphSeparator A.graphEdges part) : A.IsSeparator part :=
  fun q a q' i j hd hi hj => h q q' i j ⟨q, q', a, hd, rfl⟩ hi hj

/-- Proposition `small_delta`: `Δ ⊆ ⋃ᵢ 𝒞(Q_i) × Σ_ε × 𝒞(Q_i)`. -/
theorem small_delta [Nonempty ι] (hA : A.IsSeparator part) {q q' : Q} {a : Option α}
    (h : (q, a, q') ∈ A.delta) : ∃ i, q ∈ comp part i ∧ q' ∈ comp part i := by
  unfold comp
  rcases hq : part q with _ | i <;> rcases hq' : part q' with _ | j
  · exact ⟨Classical.arbitrary ι, by simp [hq, hq']⟩
  · exact ⟨j, by simp [hq, hq']⟩
  · exact ⟨i, by simp [hq, hq']⟩
  · obtain rfl := hA q a q' i j h hq hq'
    exact ⟨i, by simp [hq, hq']⟩

/-- A transition leaving the block `Q_i` lands in `𝒞(Q_i)`. -/
theorem mem_comp_of_delta (hA : A.IsSeparator part) {q q' : Q} {a : Option α} {i : ι}
    (h : (q, a, q') ∈ A.delta) (hq : part q = some i) : q' ∈ comp part i := by
  rcases hq' : part q' with _ | j
  · exact Or.inl hq'
  · exact Or.inr (by rw [hq', hA q a q' i j h hq hq'])

/-- Proposition (§3.1): a run between two different components passes through `X`. -/
theorem exists_sep_of_star (hA : A.IsSeparator part) {q q' : Q} {w : List α} {i j : ι}
    (h : A.Star q w q') (hq : q ∈ comp part i) (hq' : q' ∈ comp part j) (hij : i ≠ j) :
    ∃ x ∈ sepX part, ∃ w₁ w₂, w = w₁ ++ w₂ ∧ A.Star q w₁ x ∧ A.Star x w₂ q' := by
  -- Either the run stays in `𝒞(Q_i)`, or it has already visited `X`.
  have key : ∀ {q'' w}, A.Star q w q'' → q'' ∈ comp part i ∨
      ∃ x ∈ sepX part, ∃ w₁ w₂, w = w₁ ++ w₂ ∧ A.Star q w₁ x ∧ A.Star x w₂ q'' := by
    intro q'' w h
    induction h with
    | refl => exact Or.inl hq
    | @tail q₂ q₃ w a h₁ h₂ ih =>
      rcases ih with hc | ⟨x, hx, w₁, w₂, rfl, h₁', h₂'⟩
      · rcases hc with hn | hs
        · exact Or.inr ⟨q₂, hn, w, a.toList, rfl, h₁, Star.single h₂⟩
        · exact Or.inl (mem_comp_of_delta hA h₂ hs)
      · exact Or.inr ⟨x, hx, w₁, w₂ ++ a.toList, by simp, h₁', h₂'.tail h₂⟩
  rcases key h with hc | hx
  · rcases hq' with hn | hs
    · exact ⟨q', hn, w, [], by simp, h, Star.refl _⟩
    · rcases hc with hn | hs'
      · exact ⟨q', hn, w, [], by simp, h, Star.refl _⟩
      · exact absurd (Option.some_injective _ (hs'.symm.trans hs)) hij
  · exact hx

/-- The component `ε`-closure `Δ̂ᵢ_ε(P) = Δ̂_ε(P) ∩ 𝒞(Q_i)`. -/
def compClose (A : FSA α Q) (part : Q → Option ι) (i : ι) (P : Set Q) : Set Q :=
  {q | q ∈ comp part i ∧ ∃ p ∈ P, A.Star p [] q}

theorem compClose_subset (i : ι) (P : Set Q) : A.compClose part i P ⊆ comp part i :=
  fun _ h => h.1

theorem compClose_mono (i : ι) {P P' : Set Q} (h : P ⊆ P') :
    A.compClose part i P ⊆ A.compClose part i P' := by
  rintro q ⟨hq, p, hp, hs⟩; exact ⟨hq, p, h hp, hs⟩

/-- Proposition (§3.1): `ε`-runs from `Δ̂ᵢ_ε(P)` start, up to an `ε`-run, in `P`. -/
theorem exists_of_compClose {i : ι} {P : Set Q} {q'' q''' : Q}
    (h : q'' ∈ A.compClose part i P) (h' : A.Star q'' [] q''') :
    ∃ q' ∈ P, A.Star q' [] q''' := by
  obtain ⟨_, p, hp, hs⟩ := h
  exact ⟨p, hp, hs.eps_trans h'⟩

/-- Proposition (§3.1): `Δ̂ᵢ_ε(Δ̂ᵢ_ε(P) ∩ X) ⊆ Δ̂ᵢ_ε(P)`. -/
theorem compClose_compClose_inter_subset (i : ι) (P : Set Q) :
    A.compClose part i (A.compClose part i P ∩ sepX part) ⊆ A.compClose part i P := by
  rintro q ⟨hq, p, ⟨hp, -⟩, hs⟩
  obtain ⟨p', hp', hs'⟩ := exists_of_compClose hp hs
  exact ⟨hq, p', hp', hs'⟩

/-- Proposition (§3.1): for `i ≠ j` and `P ⊆ 𝒞(Q_j)`,
`Δ̂ᵢ_ε(P) = Δ̂ᵢ_ε(Δ̂ʲ_ε(P) ∩ X)`. -/
theorem compClose_eq_of_ne (hA : A.IsSeparator part) {i j : ι} (hij : i ≠ j) {P : Set Q}
    (hP : P ⊆ comp part j) :
    A.compClose part i P = A.compClose part i (A.compClose part j P ∩ sepX part) := by
  ext q
  constructor
  · rintro ⟨hq, p, hp, hs⟩
    obtain ⟨x, hx, w₁, w₂, hw, h₁, h₂⟩ := exists_sep_of_star hA hs (hP hp) hq (Ne.symm hij)
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw.symm
    exact ⟨hq, x, ⟨⟨sepX_subset_comp j hx, p, hp, h₁⟩, hx⟩, h₂⟩
  · rintro ⟨hq, p, ⟨hp, -⟩, hs⟩
    obtain ⟨p', hp', hs'⟩ := exists_of_compClose hp hs
    exact ⟨hq, p', hp', hs'⟩

end FSA

end Sqdfsa
