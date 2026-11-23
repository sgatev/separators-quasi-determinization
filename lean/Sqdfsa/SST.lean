import Sqdfsa.Lcp

/-!
# Subsequential finite-state transducers (thesis §2.6)

`δ` and `λ` are total (the thesis requires `dom(λ) = dom(δ)`); `ψ` is total but only read on
final states. Mohri's theorem (cited, not proved in the thesis) is not formalized.
-/

namespace Sqdfsa

structure SST (α β Q : Type*) where
  start : Q
  final : Set Q
  delta : Q → α → Q
  lam : Q → α → List β
  psi : Q → List β

namespace SST

variable {α β Q : Type*} (T : SST α β Q)

def deltaStar (q : Q) (w : List α) : Q := w.foldl T.delta q

/-- `λ*`, defined by consing; `lamStar_append_singleton` is the thesis' recursion. -/
def lamStar : Q → List α → List β
  | _, [] => []
  | q, a :: w => T.lam q a ++ lamStar (T.delta q a) w

@[simp] theorem deltaStar_nil (q : Q) : T.deltaStar q [] = q := rfl
@[simp] theorem deltaStar_cons (q : Q) (a : α) (w : List α) :
    T.deltaStar q (a :: w) = T.deltaStar (T.delta q a) w := rfl

theorem deltaStar_append_singleton (q : Q) (w : List α) (a : α) :
    T.deltaStar q (w ++ [a]) = T.delta (T.deltaStar q w) a := by
  simp [deltaStar]

theorem lamStar_append_singleton (q : Q) (w : List α) (a : α) :
    T.lamStar q (w ++ [a]) = T.lamStar q w ++ T.lam (T.deltaStar q w) a := by
  induction w generalizing q with
  | nil => simp [lamStar]
  | cons b w ih => simp [lamStar, ih]

/-- Paths in a subsequential transducer. -/
inductive IsPath : Q → List α → List β → Q → Prop
  | nil (q : Q) : IsPath q [] [] q
  | cons (q : Q) (a : α) {w : List α} {v : List β} {q' : Q} :
      IsPath (T.delta q a) w v q' → IsPath q (a :: w) (T.lam q a ++ v) q'

/-- Proposition (§2.6): a path from `q` to `q'` labelled `⟨u, v⟩` exists iff
`q' = δ*(q, u)` and `v = λ*(q, u)`. -/
theorem isPath_iff {q q' : Q} {u : List α} {v : List β} :
    T.IsPath q u v q' ↔ q' = T.deltaStar q u ∧ v = T.lamStar q u := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | cons q a _ ih => exact ⟨ih.1, by rw [ih.2]; rfl⟩
  · rintro ⟨rfl, rfl⟩
    induction u generalizing q with
    | nil => exact IsPath.nil q
    | cons a w ih => exact IsPath.cons q a (ih (q := T.delta q a))

/-- The function `𝓕_T` recognized by `T`, as a relation. -/
def relation : Set (List α × List β) :=
  {p | T.deltaStar T.start p.1 ∈ T.final ∧
    p.2 = T.lamStar T.start p.1 ++ T.psi (T.deltaStar T.start p.1)}

theorem relation_functional (u : List α) (v v' : List β) (h : (u, v) ∈ T.relation)
    (h' : (u, v') ∈ T.relation) : v = v' := h.2.trans h'.2.symm

end SST

end Sqdfsa
