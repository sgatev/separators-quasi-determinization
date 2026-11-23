import Sqdfsa.FSA

/-!
# Quasi-deterministic finite-state automata (thesis §3.3, §3.4)

A `k`-separated QDFA `⟨Σ, Q, X, s, F, τ, ρ, η, η_x⟩`. Each component `⟨Σ, Q_i, s_i, F_i, τ_i⟩`
is a DFA with total transition function.

Deviations from the thesis:
* `ρ_i` is total on `Q_i` (the thesis restricts its domain to `rng(τ_i)`; values outside it are
  never used).
* The inclusion `X ⊆ Q_i` is dropped: it is not used by any result.
-/

namespace Sqdfsa

universe u v w

structure QDFA (α : Type u) (k : ℕ) (Q : Fin k → Type v) (X : Type w) where
  start : ∀ i, Q i
  final : ∀ i, Set (Q i)
  tau : ∀ i, Q i → α → Q i
  rho : ∀ i, Q i → X
  eta : ∀ i, Q i → X → Q i
  etaX : X → X → X

/-- Iterated separator extension `η_x^k(x_1, …, x_k)`, a left fold starting from `x_1`. -/
def iterEtaX {X : Type w} {k : ℕ} [NeZero k] (f : X → X → X) (r : Fin k → X) : X :=
  ((List.finRange k).map r).tail.foldl f (r 0)

theorem iterEtaX_one {X : Type w} (f : X → X → X) (r : Fin 1 → X) : iterEtaX f r = r 0 := by
  simp [iterEtaX, List.finRange_succ]

/-- When `η_x` is a union, so is its iteration. -/
theorem mem_iterEtaX {β : Type*} {X : Type w} {k : ℕ} [NeZero k] (f : X → X → X)
    (val : X → Set β) (hf : ∀ a b, val (f a b) = val a ∪ val b) (r : Fin k → X) (x : β) :
    x ∈ val (iterEtaX f r) ↔ ∃ i, x ∈ val (r i) := by
  have fold : ∀ (l : List X) (a : X), x ∈ val (l.foldl f a) ↔ x ∈ val a ∨ ∃ y ∈ l, x ∈ val y := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih =>
      intro a
      simp only [List.foldl_cons, ih, hf, Set.mem_union, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨z, hz, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨y, Or.inl rfl, h⟩
        · exact Or.inr ⟨z, Or.inr hz, h⟩
      · rintro (h | ⟨z, rfl | hz, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨z, hz, h⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  rw [iterEtaX, fold]
  simp only [List.finRange_succ, List.map_cons, List.tail_cons, List.map_map, List.mem_map,
    List.mem_finRange, true_and, Function.comp_apply]
  constructor
  · rintro (h | ⟨_, ⟨j, rfl⟩, h⟩)
    · exact ⟨0, h⟩
    · exact ⟨j.succ, h⟩
  · rintro ⟨i, h⟩
    cases i using Fin.cases with
    | zero => exact Or.inl h
    | succ j => exact Or.inr ⟨_, ⟨j, rfl⟩, h⟩

namespace QDFA

variable {α : Type u} {k : ℕ} [NeZero k] {Q : Fin k → Type v} {X : Type w} (M : QDFA α k Q X)

/-- The separator state transition function `δ_x`. -/
def deltaX (q : ∀ i, Q i) (a : α) : X := iterEtaX M.etaX fun i => M.rho i (M.tau i (q i) a)

/-- The state transition function `δ = ⟨δ_1, …, δ_k⟩`, with
`δ_i(q, σ) = η_i(τ_i(q^i, σ), δ_x(q, σ))`. -/
def delta (q : ∀ i, Q i) (a : α) : ∀ i, Q i := fun i => M.eta i (M.tau i (q i) a) (M.deltaX q a)

/-- The generalized state transition function `δ*`. -/
def deltaStar (q : ∀ i, Q i) (w : List α) : ∀ i, Q i := w.foldl M.delta q

@[simp] theorem deltaStar_nil (q : ∀ i, Q i) : M.deltaStar q [] = q := rfl

@[simp] theorem deltaStar_cons (q : ∀ i, Q i) (a : α) (w : List α) :
    M.deltaStar q (a :: w) = M.deltaStar (M.delta q a) w := rfl

theorem deltaStar_append_singleton (q : ∀ i, Q i) (w : List α) (a : α) :
    M.deltaStar q (w ++ [a]) = M.delta (M.deltaStar q w) a := by
  simp [deltaStar]

/-- Paths in a QDFA, built by consing transitions. -/
inductive IsPath : (∀ i, Q i) → List α → (∀ i, Q i) → Prop
  | nil (q : ∀ i, Q i) : IsPath q [] q
  | cons (q : ∀ i, Q i) (a : α) {w : List α} {q' : ∀ i, Q i} :
      IsPath (M.delta q a) w q' → IsPath q (a :: w) q'

/-- Proposition (§3.3): there is a path from `q'` to `q''` labelled `w` iff `δ*(q', w) = q''`. -/
theorem isPath_iff {q q' : ∀ i, Q i} {w : List α} : M.IsPath q w q' ↔ M.deltaStar q w = q' := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons q a _ ih => exact ih
  · rintro rfl
    induction w generalizing q with
    | nil => exact IsPath.nil q
    | cons a w ih => exact IsPath.cons q a (ih (q := M.delta q a))

/-- The language `𝓛_A = {w | ∃ i, δ*(s, w)^i ∈ F_i}`. -/
def language : Language α := {w | ∃ i, M.deltaStar M.start w i ∈ M.final i}

/-! ### Equivalence with DFAs -/

/-- Lemma `quasidet_equiv_left`: the DFA on `∏ Q_i` with `F' = ⋃ᵢ Q_1 × … × F_i × … × Q_k`. -/
def toDFA : DFA α (∀ i, Q i) where
  step := M.delta
  start := M.start
  accept := {q | ∃ i, q i ∈ M.final i}

theorem toDFA_accepts : M.toDFA.accepts = M.language := by
  ext w
  rfl

/-- Lemma `quasidet_equiv_right`: a DFA as a `1`-separated QDFA with `X = Q`,
`ρ = id`, `η(q, p) = q`, `η_x(q, p) = q`. -/
def ofDFA {σ : Type v} (D : DFA α σ) : QDFA α 1 (fun _ => σ) σ where
  start _ := D.start
  final _ := D.accept
  tau _ := D.step
  rho _ := id
  eta _ q _ := q
  etaX q _ := q

theorem ofDFA_deltaStar {σ : Type v} (D : DFA α σ) (q : Fin 1 → σ) (w : List α) :
    (ofDFA D).deltaStar q w = fun _ => D.evalFrom (q 0) w := by
  induction w generalizing q with
  | nil => funext i; rw [Subsingleton.elim i 0]; rfl
  | cons a w ih => rw [deltaStar_cons, ih]; rfl

theorem ofDFA_language {σ : Type v} (D : DFA α σ) : (ofDFA D).language = D.accepts := by
  ext w
  simp only [language, ofDFA_deltaStar, DFA.mem_accepts, DFA.eval]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

end QDFA

/-- Theorem (§3.3): finite `k`-separated QDFAs (for some `k > 0`) and finite DFAs recognize the
same class of languages. -/
theorem qdfa_iff_dfa {α : Type u} (L : Language α) :
    (∃ (k : ℕ) (_ : NeZero k) (Q : Fin k → Type) (X : Type) (_ : ∀ i, Finite (Q i))
      (_ : Finite X) (M : QDFA α k Q X), M.language = L) ↔
    (∃ (σ : Type) (_ : Finite σ) (D : DFA α σ), D.accepts = L) := by
  constructor
  · rintro ⟨k, _, Q, X, _, _, M, rfl⟩
    exact ⟨∀ i, Q i, inferInstance, M.toDFA, M.toDFA_accepts⟩
  · rintro ⟨σ, _, D, rfl⟩
    exact ⟨1, inferInstance, fun _ => σ, σ, fun _ => inferInstance, inferInstance,
      QDFA.ofDFA D, QDFA.ofDFA_language D⟩

/-! ### Traversal (thesis §3.4, Algorithm `qdfsa_traversal`) -/

namespace QDFA

variable {α : Type u} {k : ℕ} [NeZero k] {Q : Fin k → Type v} {X : Type w} (M : QDFA α k Q X)

/-- Algorithm `qdfsa_traversal`, written as a fold over the input. Since the `τ_i` are total,
the "undefined" check of the thesis' pseudocode never fires. -/
def traverse [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) : Bool :=
  let q := w.foldl (fun q a =>
    let t := fun i => M.tau i (q i) a
    let x := iterEtaX M.etaX fun i => M.rho i (t i)
    fun i => M.eta i (t i) x) M.start
  decide (∃ i, q i ∈ M.final i)

theorem traverse_iff [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) :
    M.traverse w = true ↔ w ∈ M.language := by
  simp only [traverse, decide_eq_true_eq]
  rfl

end QDFA

end Sqdfsa
