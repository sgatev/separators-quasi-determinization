import Sqdfsa.Words

/-!
# Longest common prefixes, sequential distance, bounded variation (thesis §2.3)

The thesis defines `⋀ wᵢ` as an `argmax`. We use the equivalent characterization:
`m` is the lcp of `W` iff the common prefixes of `W` are exactly the prefixes of `m`
(`IsLcp`). For possibly-empty (and possibly infinite) sets, `setLcp W : Option (List β)` is
`none` exactly when `W = ∅`.
-/

namespace Sqdfsa

variable {β : Type*} [DecidableEq β]

/-- Longest common prefix of two words. -/
def lcp : List β → List β → List β
  | a :: as, b :: bs => if a = b then a :: lcp as bs else []
  | _, _ => []

theorem prefix_lcp_iff {c a b : List β} : c <+: lcp a b ↔ c <+: a ∧ c <+: b := by
  induction a generalizing b c with
  | nil => cases c <;> simp [lcp]
  | cons x as ih =>
    cases b with
    | nil => cases c <;> simp [lcp]
    | cons y bs =>
      cases c with
      | nil => simp
      | cons z cs =>
        simp only [lcp]
        split_ifs with h
        · subst h
          simp only [List.cons_prefix_cons, ih]
          tauto
        · simp only [List.cons_prefix_cons]
          constructor
          · intro h'; simp at h'
          · rintro ⟨⟨rfl, -⟩, rfl, -⟩; exact absurd rfl h

theorem lcp_prefix_left (a b : List β) : lcp a b <+: a :=
  (prefix_lcp_iff.mp (List.prefix_refl _)).1

theorem lcp_prefix_right (a b : List β) : lcp a b <+: b :=
  (prefix_lcp_iff.mp (List.prefix_refl _)).2

theorem lcp_append_left (o x y : List β) : lcp (o ++ x) (o ++ y) = o ++ lcp x y := by
  induction o with
  | nil => rfl
  | cons a o ih => simp [lcp, ih]

theorem lcp_cons_cons_of_ne {x y : β} (h : x ≠ y) (xs ys : List β) :
    lcp (x :: xs) (y :: ys) = [] := by
  simp [lcp, h]

theorem lcp_nil_left (b : List β) : lcp [] b = [] := by cases b <;> rfl

/-! ### Lcp of a set of words -/

/-- `m` is the longest common prefix of `W`. -/
def IsLcp (W : Set (List β)) (m : List β) : Prop := ∀ c, (∀ w ∈ W, c <+: w) ↔ c <+: m

/-- `m` is the lcp of `W`, with `none` standing for `W = ∅`. -/
def OIsLcp (W : Set (List β)) : Option (List β) → Prop
  | none => W = ∅
  | some m => W.Nonempty ∧ IsLcp W m

omit [DecidableEq β] in
theorem IsLcp.prefix {W : Set (List β)} {m : List β} (h : IsLcp W m) {w : List β} (hw : w ∈ W) :
    m <+: w :=
  (h m).mpr (List.prefix_refl m) w hw

omit [DecidableEq β] in
theorem exists_isLcp {W : Set (List β)} (h : W.Nonempty) : ∃ m, IsLcp W m := by
  classical
  obtain ⟨w₀, hw₀⟩ := h
  let P : ℕ → Prop := fun n => ∀ w ∈ W, w₀.take n <+: w
  let n := Nat.findGreatest P w₀.length
  have hn : P n := Nat.findGreatest_spec (P := P) (Nat.zero_le _) (by simp [P])
  refine ⟨w₀.take n, fun c => ⟨fun hc => ?_, fun hc w hw => hc.trans (hn w hw)⟩⟩
  have hc₀ : c <+: w₀ := hc w₀ hw₀
  have hct : c = w₀.take c.length := List.prefix_iff_eq_take.mp hc₀
  have hle : c.length ≤ n :=
    Nat.le_findGreatest hc₀.length_le (by intro w hw; rw [← hct]; exact hc w hw)
  rw [hct, ← Nat.min_eq_left hle, ← List.take_take]
  exact List.take_prefix _ _

/-- The lcp of a set of words; `none` for the empty set. -/
noncomputable def setLcp (W : Set (List β)) : Option (List β) :=
  open Classical in if h : W.Nonempty then some (Classical.choose (exists_isLcp h)) else none

omit [DecidableEq β] in
theorem setLcp_spec (W : Set (List β)) : OIsLcp W (setLcp W) := by
  unfold setLcp
  split_ifs with h
  · exact ⟨h, Classical.choose_spec (exists_isLcp h)⟩
  · exact Set.not_nonempty_iff_eq_empty.mp h

/-- Lcp on `Option`, with `none` neutral. -/
def olcp : Option (List β) → Option (List β) → Option (List β)
  | none, b => b
  | some a, none => some a
  | some a, some b => some (lcp a b)

theorem OIsLcp.union {W W' : Set (List β)} {a b : Option (List β)} (ha : OIsLcp W a)
    (hb : OIsLcp W' b) : OIsLcp (W ∪ W') (olcp a b) := by
  cases a <;> cases b <;> simp only [OIsLcp, olcp] at ha hb ⊢
  · rw [ha, hb, Set.union_empty]
  · rw [ha, Set.empty_union]; exact hb
  · rw [hb, Set.union_empty]; exact ha
  · refine ⟨ha.1.mono Set.subset_union_left, fun c => ?_⟩
    rw [prefix_lcp_iff, ← ha.2 c, ← hb.2 c]
    simp only [Set.mem_union]
    exact ⟨fun h => ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw)⟩,
      fun ⟨h₁, h₂⟩ w hw => hw.elim (h₁ w) (h₂ w)⟩

omit [DecidableEq β] in
theorem OIsLcp.congr {W W' : Set (List β)} {a : Option (List β)} (h : OIsLcp W a) (e : W = W') :
    OIsLcp W' a := e ▸ h

omit [DecidableEq β] in
theorem OIsLcp.eq_none_iff {W : Set (List β)} {a : Option (List β)} (h : OIsLcp W a) :
    a = none ↔ W = ∅ := by
  cases a with
  | none => simpa [OIsLcp] using h
  | some m =>
    simp only [reduceCtorEq, false_iff]
    exact h.1.ne_empty

/-! ### Sequential distance and bounded variation -/

/-- Sequential distance `d(u, v) = |u| + |v| - 2|u ∧ v|`. -/
def dist (u v : List β) : ℕ := u.length + v.length - 2 * (lcp u v).length

/-- A relation `R ⊆ Σ* × Ω*` has bounded variation (thesis §2.3, stated for relations; for a
functional relation this is the thesis' definition for the function). -/
def BoundedVariation {α : Type*} [DecidableEq α] (R : Set (List α × List β)) : Prop :=
  ∀ k, ∃ K, ∀ u v u' v', (u, v) ∈ R → (u', v') ∈ R → dist u u' ≤ k → dist v v' ≤ K

theorem dist_append_left (o x y : List β) : dist (o ++ x) (o ++ y) = dist x y := by
  unfold dist
  rw [lcp_append_left]
  have := (lcp_prefix_left x y).length_le
  have := (lcp_prefix_right x y).length_le
  simp only [List.length_append]
  omega

theorem dist_append_left_le (w x y : List β) : dist (w ++ x) (w ++ y) ≤ x.length + y.length := by
  unfold dist
  rw [lcp_append_left]
  simp only [List.length_append]
  omega

end Sqdfsa
