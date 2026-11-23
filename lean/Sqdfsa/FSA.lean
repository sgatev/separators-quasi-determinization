import Sqdfsa.Words

/-!
# Finite-state automata (thesis §2.4)

`FSA α Q` is the tuple `⟨Σ, Q, S, F, Δ⟩` with `Δ ⊆ Q × Σ_ε × Q`, where `Σ_ε` is `Option α`
(`none` is `ε`). Finiteness of `Q` is imposed by type-class assumptions only where needed.

The thesis' notion of path is identified with Mathlib's `εNFA.IsPath` via `FSA.toεNFA`, and
the Rabin–Scott theorem is taken from Mathlib (`NFA.toDFA_correct`).
-/

namespace Sqdfsa

structure FSA (α : Type*) (Q : Type*) where
  start : Set Q
  final : Set Q
  delta : Set (Q × Option α × Q)

namespace FSA

variable {α Q : Type*} (A : FSA α Q)

/-- The generalized relation of state transitions `Δ*`: the least relation containing
`⟨q, ε, q⟩` and closed under appending one transition on the right. -/
inductive Star (A : FSA α Q) : Q → List α → Q → Prop
  | refl (q : Q) : Star A q [] q
  | tail {q₁ q₂ q₃ : Q} {w : List α} {a : Option α} :
      Star A q₁ w q₂ → (q₂, a, q₃) ∈ A.delta → Star A q₁ (w ++ a.toList) q₃

variable {A}

theorem Star.single {q q' : Q} {a : Option α} (h : (q, a, q') ∈ A.delta) :
    A.Star q a.toList q' := by
  simpa using (Star.refl q).tail h

theorem Star.trans {q₁ q₂ q₃ : Q} {u v : List α} (h₁ : A.Star q₁ u q₂) (h₂ : A.Star q₂ v q₃) :
    A.Star q₁ (u ++ v) q₃ := by
  induction h₂ with
  | refl => simpa using h₁
  | tail _ h ih => simpa [List.append_assoc] using ih.tail h

theorem Star.head {q₁ q₂ q₃ : Q} {a : Option α} {w : List α} (h : (q₁, a, q₂) ∈ A.delta)
    (h' : A.Star q₂ w q₃) : A.Star q₁ (a.toList ++ w) q₃ :=
  (Star.single h).trans h'

/-- An `ε`-labelled run followed by a run. -/
theorem Star.eps_trans {q₁ q₂ q₃ : Q} {w : List α} (h₁ : A.Star q₁ [] q₂)
    (h₂ : A.Star q₂ w q₃) : A.Star q₁ w q₃ := by
  simpa using h₁.trans h₂

/-- A run labelled `w ++ [a]` splits as a run on `w`, an `a`-transition, and an `ε`-run. -/
theorem Star.snoc_iff {q₁ q₃ : Q} {w : List α} {a : α} :
    A.Star q₁ (w ++ [a]) q₃ ↔
      ∃ y z, A.Star q₁ w y ∧ (y, some a, z) ∈ A.delta ∧ A.Star z [] q₃ := by
  constructor
  · intro h
    generalize hl : w ++ [a] = l at h
    induction h generalizing w with
    | refl => simp at hl
    | @tail q₂ q₃ w' b h₁ h₂ ih =>
      cases b with
      | none =>
        obtain ⟨y, z, hy, hyz, hz⟩ := ih (by simpa using hl)
        exact ⟨y, z, hy, hyz, by simpa using hz.tail h₂⟩
      | some c =>
        simp only [Option.toList_some] at hl
        obtain ⟨rfl, hc⟩ := List.append_inj' hl rfl
        obtain rfl : a = c := by simpa using hc
        exact ⟨q₂, q₃, h₁, h₂, Star.refl _⟩
  · rintro ⟨y, z, hy, hyz, hz⟩
    simpa using (hy.tail hyz).trans hz

/-- Translation into Mathlib's `εNFA`. -/
def toεNFA (A : FSA α Q) : εNFA α Q where
  step q a := {q' | (q, a, q') ∈ A.delta}
  start := A.start
  accept := A.final

private theorem reduceOption_singleton (a : Option α) : [a].reduceOption = a.toList := by
  cases a <;> simp [List.reduceOption_cons_of_some, List.reduceOption_cons_of_none,
    List.reduceOption_nil]

private theorem reduceOption_cons (a : Option α) (x : List (Option α)) :
    (a :: x).reduceOption = a.toList ++ x.reduceOption := by
  cases a <;> simp [List.reduceOption_cons_of_some, List.reduceOption_cons_of_none]

/-- Proposition (§2.4): there is a path from `q` to `q'` labelled `w` iff `⟨q, w, q'⟩ ∈ Δ*`.
Paths are Mathlib's `εNFA.IsPath`, whose label is obtained by erasing the `ε`s. -/
theorem star_iff_exists_path {q q' : Q} {w : List α} :
    A.Star q w q' ↔ ∃ x : List (Option α), x.reduceOption = w ∧ A.toεNFA.IsPath q q' x := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl, εNFA.IsPath.nil _⟩
    | @tail q₂ q₃ w a _ h ih =>
      obtain ⟨x, rfl, hx⟩ := ih
      refine ⟨x ++ [a], by rw [List.reduceOption_append, reduceOption_singleton], ?_⟩
      exact (A.toεNFA.isPath_append).mpr ⟨q₂, hx, (A.toεNFA.isPath_singleton).mpr h⟩
  · rintro ⟨x, rfl, hx⟩
    induction hx with
    | nil q => exact Star.refl q
    | cons t s u a x h _ ih =>
      rw [reduceOption_cons]
      exact Star.head h ih

/-- The language `𝓛_A` recognized by `A`. -/
def language (A : FSA α Q) : Language α :=
  {w | ∃ s ∈ A.start, ∃ f ∈ A.final, A.Star s w f}

theorem language_eq_accepts : A.language = A.toεNFA.accepts := by
  ext w
  rw [εNFA.mem_accepts_iff_exists_path]
  simp only [language, star_iff_exists_path]
  constructor
  · rintro ⟨s, hs, f, hf, x, hx, hp⟩; exact ⟨s, f, x, hs, hf, hx, hp⟩
  · rintro ⟨s, f, x, hs, hf, hx, hp⟩; exact ⟨s, hs, f, hf, x, hx, hp⟩

/-- Theorem (Rabin, Scott), via Mathlib's subset construction. -/
theorem rabin_scott (A : FSA α Q) : ∃ M : DFA α (Set Q), M.accepts = A.language :=
  ⟨A.toεNFA.toNFA.toDFA, by rw [NFA.toDFA_correct, εNFA.toNFA_correct, language_eq_accepts]⟩

/-- The set-lifted `ε`-closure `Δ̂_ε(P)`. -/
def eclose (A : FSA α Q) (P : Set Q) : Set Q := {q | ∃ p ∈ P, A.Star p [] q}

/-- The set-lifted transition function `Δ̂_f(P, {a})`. -/
def stepSet (A : FSA α Q) (P : Set Q) (a : α) : Set Q :=
  {q | ∃ p ∈ P, (p, some a, q) ∈ A.delta}

/-! ### Graphs and separators (thesis §2.2)

A graph edge is a set `e ⊆ V` with `|e| ∈ {1, 2}`; this is exactly `Sym2 V`. -/

/-- The graph `𝒢_A = ⟨Q, E⟩` corresponding to `A`. -/
def graphEdges (A : FSA α Q) : Set (Sym2 Q) := {e | ∃ q q' a, (q, a, q') ∈ A.delta ∧ e = s(q, q')}

end FSA

/-- `part` presents a partition `{X, Q_i}` of the vertices: `part v = none` means `v ∈ X`, and
`part v = some i` means `v ∈ Q_i`. It is a separator of the graph with edge set `E` if no edge
joins two different blocks `Q_i`, `Q_j`. -/
def IsGraphSeparator {V ι : Type*} (E : Set (Sym2 V)) (part : V → Option ι) : Prop :=
  ∀ v v' i j, s(v, v') ∈ E → part v = some i → part v' = some j → i = j

end Sqdfsa
