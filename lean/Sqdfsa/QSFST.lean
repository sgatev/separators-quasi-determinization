import Sqdfsa.QDFA
import Sqdfsa.Lcp

/-!
# Quasi-subsequential finite-state transducers (thesis §4.2, §4.3)

A `k`-separated QSFST `⟨Σ, Ω, Q, X, s, F, τ, ρ, η, η_x, λ, ψ⟩`. It extends the QDFA structure
(`τ, ρ, η, η_x` and hence `δ_x, δ, δ*`) with outputs.

Partiality: the thesis' `τ_i` and `λ_i` are partial with `dom(λ_i) = dom(τ_i)`. Here `τ_i` is
total and `λ_i` returns `Option`: `none` marks "no transition". The global output
`λ(q, σ) = ⋀ᵢ λᵢ(qⁱ, σ)` ignores undefined components and is `none` when all are undefined, in
which case `δ(q, σ)` is undefined in the thesis; we record this through `λ* = none`.
-/

namespace Sqdfsa

universe u v w x

structure QSFST (α : Type u) (β : Type x) (k : ℕ) (Q : Fin k → Type v) (X : Type w) extends
    QDFA α k Q X where
  lam : ∀ i, Q i → α → Option (List β)
  psi : ∀ i, Q i → List β

namespace QSFST

variable {α : Type u} {β : Type x} [DecidableEq β] {k : ℕ} [NeZero k] {Q : Fin k → Type v}
  {X : Type w} (M : QSFST α β k Q X)

/-- The state transition output function `λ(q, σ) = ⋀ᵢ λᵢ(qⁱ, σ)`. -/
def olam (q : ∀ i, Q i) (a : α) : Option (List β) := iterEtaX olcp fun i => M.lam i (q i) a

/-- `λ*`, by consing; `lamStar_append_singleton` is the thesis' recursion. -/
def lamStar : (∀ i, Q i) → List α → Option (List β)
  | _, [] => some []
  | q, a :: w => (M.olam q a).bind fun l => (lamStar (M.delta q a) w).map (l ++ ·)

theorem lamStar_append_singleton (q : ∀ i, Q i) (w : List α) (a : α) :
    M.lamStar q (w ++ [a]) =
      (M.lamStar q w).bind fun o => (M.olam (M.deltaStar q w) a).map (o ++ ·) := by
  induction w generalizing q with
  | nil =>
    simp only [List.nil_append, lamStar, QDFA.deltaStar_nil]
    cases M.olam q a <;> simp
  | cons b w ih =>
    simp only [List.cons_append, lamStar, ih, QDFA.deltaStar_cons]
    cases M.olam q b <;> simp only [Option.bind_none, Option.bind_some]
    cases M.lamStar (M.delta q b) w <;> simp only [Option.bind_none, Option.map_none,
      Option.bind_some, Option.map_some]
    cases M.olam (M.deltaStar (M.delta q b) w) a <;> simp

/-- Proposition (§4.2): `λ(δ*(q,u),σ)⁻¹ λ*(q,u)⁻¹ v = λ*(q, uσ)⁻¹ v` whenever the left side
is defined. -/
theorem lquot_lamStar (q : ∀ i, Q i) (u : List α) (a : α) (o l : List β)
    (ho : M.lamStar q u = some o) (hl : M.olam (M.deltaStar q u) a = some l) (v : List β) :
    M.lamStar q (u ++ [a]) = some (o ++ l) ∧ lquot l (lquot o v) = lquot (o ++ l) v :=
  ⟨by simp [lamStar_append_singleton, ho, hl], left_word_factor o l v⟩

/-- Paths in a QSFST. -/
inductive IsPath : (∀ i, Q i) → List α → List β → (∀ i, Q i) → Prop
  | nil (q : ∀ i, Q i) : IsPath q [] [] q
  | cons (q : ∀ i, Q i) (a : α) {l : List β} {w : List α} {o : List β} {q' : ∀ i, Q i} :
      M.olam q a = some l → IsPath (M.delta q a) w o q' → IsPath q (a :: w) (l ++ o) q'

/-- Proposition (§4.2): a path from `q` to `q'` labelled `⟨u, v⟩` exists iff
`δ*(q, u) = q'` and `λ*(q, u) = v`. -/
theorem isPath_iff {q q' : ∀ i, Q i} {u : List α} {v : List β} :
    M.IsPath q u v q' ↔ M.deltaStar q u = q' ∧ M.lamStar q u = some v := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | cons q a hl _ ih => exact ⟨ih.1, by simp [lamStar, hl, ih.2]⟩
  · rintro ⟨rfl, hv⟩
    induction u generalizing q v with
    | nil => cases hv; exact IsPath.nil q
    | cons a w ih =>
      simp only [lamStar, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
      obtain ⟨l, hl, o, ho, rfl⟩ := hv
      exact IsPath.cons q a hl (ih ho)

/-- The relation `𝓡_T` recognized by `T`. -/
def relation : Set (List α × List β) :=
  {p | ∃ i, M.deltaStar M.start p.1 i ∈ M.final i ∧
    ∃ o, M.lamStar M.start p.1 = some o ∧ p.2 = o ++ M.psi i (M.deltaStar M.start p.1 i)}

/-! ### Traversal (Algorithm `qsfst_traversal`) and `lcp_k` (Algorithm `lcp`) -/

/-- Algorithm `lcp`: the longest common prefix of `k > 0` words. -/
def lcpK : List (List β) → List β
  | [] => []
  | w :: ws => ws.foldl lcp w

theorem prefix_lcpK_iff (c w : List β) (ws : List (List β)) :
    c <+: lcpK (w :: ws) ↔ ∀ x ∈ w :: ws, c <+: x := by
  simp only [lcpK]
  induction ws generalizing w with
  | nil => simp
  | cons y ws ih =>
    simp only [List.foldl_cons, ih, prefix_lcp_iff, List.mem_cons, forall_eq_or_imp]
    tauto

/-- Algorithm `qsfst_traversal`: translate `w`, returning the output for the first final
component (the thesis returns "one of the possible translations"). -/
def traverse [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) : Option (List β) :=
  let q := M.deltaStar M.start w
  (M.lamStar M.start w).bind fun o =>
    ((List.finRange k).find? fun i => decide (q i ∈ M.final i)).map fun i => o ++ M.psi i (q i)

theorem traverse_sound [∀ i, DecidablePred (· ∈ M.final i)] {w : List α} {v : List β}
    (h : M.traverse w = some v) : (w, v) ∈ M.relation := by
  simp only [traverse, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨o, ho, i, hi, rfl⟩ := h
  have := List.find?_some hi
  exact ⟨i, by simpa using this, o, ho, rfl⟩

theorem traverse_complete [∀ i, DecidablePred (· ∈ M.final i)] {w : List α} {v : List β}
    (h : (w, v) ∈ M.relation) : (M.traverse w).isSome := by
  obtain ⟨i, hi, o, ho, -⟩ := h
  simp only [traverse, ho, Option.bind_some, Option.isSome_map]
  rw [List.find?_isSome]
  exact ⟨i, List.mem_finRange i, by simpa using hi⟩

end QSFST

end Sqdfsa
