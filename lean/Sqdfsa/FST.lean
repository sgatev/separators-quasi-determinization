import Sqdfsa.Separated
import Sqdfsa.Lcp

/-!
# Finite-state transducers (thesis §2.5) and separated transducers (§4.1)

`FST α β Q` is `⟨Σ, Ω, Q, S, F, Δ⟩` with `Δ ⊆ Q × Σ_ε × Ω* × Q`.
-/

namespace Sqdfsa

structure FST (α β Q : Type*) where
  start : Set Q
  final : Set Q
  delta : Set (Q × Option α × List β × Q)

namespace FST

variable {α β Q ι : Type*}

/-- The generalized relation of state transitions `Δ*`. -/
inductive Star (T : FST α β Q) : Q → List α → List β → Q → Prop
  | refl (q : Q) : Star T q [] [] q
  | tail {q₁ q₂ q₃ : Q} {w : List α} {u : List β} {a : Option α} {v : List β} :
      Star T q₁ w u q₂ → (q₂, a, v, q₃) ∈ T.delta → Star T q₁ (w ++ a.toList) (u ++ v) q₃

variable {T : FST α β Q}

theorem Star.single {q q' : Q} {a : Option α} {v : List β} (h : (q, a, v, q') ∈ T.delta) :
    T.Star q a.toList v q' := by
  simpa using (Star.refl q).tail h

theorem Star.trans {q₁ q₂ q₃ : Q} {w w' : List α} {u u' : List β} (h₁ : T.Star q₁ w u q₂)
    (h₂ : T.Star q₂ w' u' q₃) : T.Star q₁ (w ++ w') (u ++ u') q₃ := by
  induction h₂ with
  | refl => simpa using h₁
  | tail _ h ih => simpa [List.append_assoc] using ih.tail h

theorem Star.head {q₁ q₂ q₃ : Q} {a : Option α} {v : List β} {w : List α} {u : List β}
    (h : (q₁, a, v, q₂) ∈ T.delta) (h' : T.Star q₂ w u q₃) :
    T.Star q₁ (a.toList ++ w) (v ++ u) q₃ :=
  (Star.single h).trans h'

theorem Star.eps_trans {q₁ q₂ q₃ : Q} {w : List α} {u u' : List β} (h₁ : T.Star q₁ [] u q₂)
    (h₂ : T.Star q₂ w u' q₃) : T.Star q₁ w (u ++ u') q₃ := by
  simpa using h₁.trans h₂

theorem Star.trans_eps {q₁ q₂ q₃ : Q} {w : List α} {u u' : List β} (h₁ : T.Star q₁ w u q₂)
    (h₂ : T.Star q₂ [] u' q₃) : T.Star q₁ w (u ++ u') q₃ := by
  simpa using h₁.trans h₂

/-- A run labelled `w ++ [a]` splits at its last `a`-transition. -/
theorem Star.snoc_iff {q₁ q₃ : Q} {w : List α} {a : α} {out : List β} :
    T.Star q₁ (w ++ [a]) out q₃ ↔
      ∃ y z o₁ o₂ o₃, out = o₁ ++ o₂ ++ o₃ ∧ T.Star q₁ w o₁ y ∧ (y, some a, o₂, z) ∈ T.delta ∧
        T.Star z [] o₃ q₃ := by
  constructor
  · intro h
    generalize hl : w ++ [a] = l at h
    induction h generalizing w with
    | refl => simp at hl
    | @tail q₂ q₃ w' u b v h₁ h₂ ih =>
      cases b with
      | none =>
        obtain ⟨y, z, o₁, o₂, o₃, rfl, hy, hyz, hz⟩ := ih (by simpa using hl)
        exact ⟨y, z, o₁, o₂, o₃ ++ v, by simp, hy, hyz, by simpa using hz.tail h₂⟩
      | some c =>
        simp only [Option.toList_some] at hl
        obtain ⟨rfl, hc⟩ := List.append_inj' hl rfl
        obtain rfl : a = c := by simpa using hc
        exact ⟨q₂, q₃, u, v, [], by simp, h₁, h₂, Star.refl _⟩
  · rintro ⟨y, z, o₁, o₂, o₃, rfl, hy, hyz, hz⟩
    simpa [List.append_assoc] using (hy.tail hyz).trans hz

/-! ### Paths -/

/-- Paths, as lists of transition labels `⟨σ, w⟩`, built by consing. -/
inductive IsPath (T : FST α β Q) : Q → Q → List (Option α × List β) → Prop
  | nil (q : Q) : IsPath T q q []
  | cons {q q' q'' : Q} {a : Option α} {v : List β} {l : List (Option α × List β)} :
      (q, a, v, q') ∈ T.delta → IsPath T q' q'' l → IsPath T q q'' ((a, v) :: l)

/-- The label `⟨σ₁…σₙ, w₁…wₙ⟩` of a path. -/
def label (l : List (Option α × List β)) : List α × List β :=
  ((l.map Prod.fst).reduceOption, (l.map Prod.snd).flatten)

theorem IsPath.append {q q' q'' : Q} {l l' : List (Option α × List β)} (h : T.IsPath q q' l)
    (h' : T.IsPath q' q'' l') : T.IsPath q q'' (l ++ l') := by
  induction h with
  | nil => exact h'
  | cons hd _ ih => exact IsPath.cons hd (ih h')

private theorem reduceOption_cons' (a : Option α) (x : List (Option α)) :
    (a :: x).reduceOption = a.toList ++ x.reduceOption := by
  cases a <;> simp [List.reduceOption_cons_of_some, List.reduceOption_cons_of_none]

/-- Proposition (§2.5): there is a path from `q` to `q'` labelled `⟨u, v⟩` iff
`⟨q, u, v, q'⟩ ∈ Δ*`. -/
theorem star_iff_exists_path {q q' : Q} {u : List α} {v : List β} :
    T.Star q u v q' ↔ ∃ l, label l = (u, v) ∧ T.IsPath q q' l := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl, IsPath.nil _⟩
    | @tail q₂ q₃ w u a v _ h ih =>
      obtain ⟨l, hl, hp⟩ := ih
      simp only [label, Prod.mk.injEq] at hl
      refine ⟨l ++ [(a, v)], ?_, hp.append (IsPath.cons h (IsPath.nil _))⟩
      simp only [label, List.map_append, List.map_cons, List.map_nil, List.reduceOption_append,
        List.flatten_append, hl.1, hl.2]
      cases a <;> simp [List.reduceOption_cons_of_some, List.reduceOption_cons_of_none]
  · rintro ⟨l, hl, hp⟩
    induction hp generalizing u v with
    | nil => simp only [label, List.map_nil, List.reduceOption_nil, List.flatten_nil,
        Prod.mk.injEq] at hl; rw [← hl.1, ← hl.2]; exact Star.refl _
    | @cons q₁ q₂ q₃ a v' l h _ ih =>
      simp only [label, List.map_cons, reduceOption_cons', List.flatten_cons,
        Prod.mk.injEq] at hl
      rw [← hl.1, ← hl.2]
      exact Star.head h (ih rfl)

/-! ### Relations and properties -/

/-- The relation `𝓡_T` recognized by `T`. -/
def relation (T : FST α β Q) : Set (List α × List β) :=
  {p | ∃ s ∈ T.start, ∃ f ∈ T.final, T.Star s p.1 p.2 f}

/-- `T` is functional: `𝓡_T` is the graph of a (partial) function. -/
def IsFunctional (T : FST α β Q) : Prop :=
  ∀ u v v', (u, v) ∈ T.relation → (u, v') ∈ T.relation → v = v'

/-- `T` is trimmed: every state is accessible and co-accessible. -/
def IsTrimmed (T : FST α β Q) : Prop :=
  ∀ q, (∃ s ∈ T.start, ∃ u v, T.Star s u v q) ∧ (∃ f ∈ T.final, ∃ u v, T.Star q u v f)

/-- The output `ε`-closure `Δ̂_ε(P)` of a set of (state, pending output) pairs. -/
def eclose (T : FST α β Q) (P : Set (Q × List β)) : Set (Q × List β) :=
  {x | ∃ p ∈ P, ∃ v, T.Star p.1 [] v x.1 ∧ x.2 = p.2 ++ v}

/-- The graph `𝒢_T` corresponding to `T`. -/
def graphEdges (T : FST α β Q) : Set (Sym2 Q) :=
  {e | ∃ q q' a v, (q, a, v, q') ∈ T.delta ∧ e = s(q, q')}

/-! ### Separated transducers (§4.1) -/

/-- `X` is a separator in `T` (partition given by `part`, as for automata). -/
def IsSeparator (T : FST α β Q) (part : Q → Option ι) : Prop :=
  ∀ q a v q' i j, (q, a, v, q') ∈ T.delta → part q = some i → part q' = some j → i = j

variable {part : Q → Option ι}

/-- Proposition (§4.1): a separator in `𝒢_T` is a separator in `T`. -/
theorem isSeparator_of_graph (h : IsGraphSeparator T.graphEdges part) : T.IsSeparator part :=
  fun q a v q' i j hd hi hj => h q q' i j ⟨q, q', a, v, hd, rfl⟩ hi hj

/-- Proposition (§4.1): `Δ ⊆ ⋃ᵢ 𝒞(Q_i) × Σ_ε × Ω* × 𝒞(Q_i)`. -/
theorem small_delta [Nonempty ι] (hT : T.IsSeparator part) {q q' : Q} {a : Option α}
    {v : List β} (h : (q, a, v, q') ∈ T.delta) : ∃ i, q ∈ comp part i ∧ q' ∈ comp part i := by
  unfold comp
  rcases hq : part q with _ | i <;> rcases hq' : part q' with _ | j
  · exact ⟨Classical.arbitrary ι, by simp [hq, hq']⟩
  · exact ⟨j, by simp [hq, hq']⟩
  · exact ⟨i, by simp [hq, hq']⟩
  · obtain rfl := hT q a v q' i j h hq hq'
    exact ⟨i, by simp [hq, hq']⟩

theorem mem_comp_of_delta (hT : T.IsSeparator part) {q q' : Q} {a : Option α} {v : List β}
    {i : ι} (h : (q, a, v, q') ∈ T.delta) (hq : part q = some i) : q' ∈ comp part i := by
  rcases hq' : part q' with _ | j
  · exact Or.inl hq'
  · exact Or.inr (by rw [hq', hT q a v q' i j h hq hq'])

/-- Proposition (§4.1): a run between two different components passes through `X`, splitting
both its input and its output. -/
theorem exists_sep_of_star (hT : T.IsSeparator part) {q q' : Q} {u : List α} {v : List β}
    {i j : ι} (h : T.Star q u v q') (hq : q ∈ comp part i) (hq' : q' ∈ comp part j)
    (hij : i ≠ j) :
    ∃ x ∈ sepX part, ∃ u₁ u₂ v₁ v₂, u = u₁ ++ u₂ ∧ v = v₁ ++ v₂ ∧ T.Star q u₁ v₁ x ∧
      T.Star x u₂ v₂ q' := by
  have key : ∀ {q'' u v}, T.Star q u v q'' → q'' ∈ comp part i ∨
      ∃ x ∈ sepX part, ∃ u₁ u₂ v₁ v₂, u = u₁ ++ u₂ ∧ v = v₁ ++ v₂ ∧ T.Star q u₁ v₁ x ∧
        T.Star x u₂ v₂ q'' := by
    intro q'' u v h
    induction h with
    | refl => exact Or.inl hq
    | @tail q₂ q₃ w o a v' h₁ h₂ ih =>
      rcases ih with hc | ⟨x, hx, u₁, u₂, v₁, v₂, rfl, rfl, h₁', h₂'⟩
      · rcases hc with hn | hs
        · exact Or.inr ⟨q₂, hn, w, a.toList, o, v', rfl, rfl, h₁, Star.single h₂⟩
        · exact Or.inl (mem_comp_of_delta hT h₂ hs)
      · exact Or.inr ⟨x, hx, u₁, u₂ ++ a.toList, v₁, v₂ ++ v', by simp, by simp, h₁',
          h₂'.tail h₂⟩
  rcases key h with hc | hx
  · have hsep : q' ∈ sepX part := by
      rcases hq' with hn | hs
      · exact hn
      · rcases hc with hn | hs'
        · exact hn
        · exact absurd (Option.some_injective _ (hs'.symm.trans hs)) hij
    exact ⟨q', hsep, u, [], v, [], by simp, by simp, h, Star.refl _⟩
  · exact hx

/-- An `ε`-run between two different components passes through `X`. -/
theorem exists_sep_of_eps (hT : T.IsSeparator part) {q q' : Q} {v : List β} {i j : ι}
    (h : T.Star q [] v q') (hq : q ∈ comp part i) (hq' : q' ∈ comp part j) (hij : i ≠ j) :
    ∃ x ∈ sepX part, ∃ v₁ v₂, v = v₁ ++ v₂ ∧ T.Star q [] v₁ x ∧ T.Star x [] v₂ q' := by
  obtain ⟨x, hx, u₁, u₂, v₁, v₂, hu, hv, h₁, h₂⟩ := exists_sep_of_star hT h hq hq' hij
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hu.symm
  exact ⟨x, hx, v₁, v₂, hv, h₁, h₂⟩

/-- The component output `ε`-closure `Δ̂ᵢ_ε(P)`. -/
def compClose (T : FST α β Q) (part : Q → Option ι) (i : ι) (P : Set (Q × List β)) :
    Set (Q × List β) :=
  {x | x.1 ∈ comp part i ∧ x ∈ T.eclose P}

/-- The component transition `ε`-closure `Δ̂ᵢ_{fε}(P, σ)`: read `σ` (with surrounding
`ε`-moves) from a pair of `P`, accumulating output, and land in `𝒞(Q_i)`. -/
def compStep (T : FST α β Q) (part : Q → Option ι) (i : ι) (P : Set (Q × List β)) (a : α) :
    Set (Q × List β) :=
  {x | x.1 ∈ comp part i ∧ ∃ p ∈ P, ∃ v, T.Star p.1 [a] v x.1 ∧ x.2 = p.2 ++ v}

end FST

end Sqdfsa
