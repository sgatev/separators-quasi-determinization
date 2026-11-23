import Sqdfsa.QuasiSubseq

/-!
# Complexity of the traversal algorithms (thesis §3.4, §4.3)

**Cost model.** As in the thesis, every table lookup (`τ_i`, `ρ_i`, `η_i`, `η_x`, `λ_i`, `ψ_i`),
membership test, symbol comparison, and word concatenation costs one step. Each algorithm is
written as a function returning its result together with the number of steps. The step counts
follow the thesis' line-by-line accounting. Each instrumented algorithm is proved to compute the
same result as its specification, and its step count is bounded.

Results:
* `QDFA.traverseT`: Algorithm `qdfsa_traversal` takes exactly `1 + 5kn + k` steps (`O(kn)`).
* `lcpCols`: Algorithm `lcp` (column scan with early exit) takes at most
  `(|p| + 2)·k` steps, where `p` is the result. Since `|p| ≤ min |wᵢ|`, this is `O(k(n + 1))`.
  The thesis states `O(kn)`; the `+1` is needed because the minimum-length computation alone
  takes `k - 1` steps.
* `QSFST.traverseT`: Algorithm `qsfst_traversal` takes at most `12k(n + 1) + k|v|` steps when it
  returns `v`, i.e. `O(k(n + m))`. The proof needs early exit in Algorithm `lcp`: the cost of
  step `i` is `O(k(|pᵢ| + 1))`, and `Σ|pᵢ| ≤ |v|`. The thesis' per-call bound `O(k·min|lⱼ|)`
  does not sum to `O(km)`, because `min|lⱼ|` can be much longer than the common prefix.
-/

namespace Sqdfsa

/-! ### Algorithm `qdfsa_traversal` -/

namespace QDFA

universe u v w

variable {α : Type u} {k : ℕ} [NeZero k] {Q : Fin k → Type v} {X : Type w} (M : QDFA α k Q X)

/-- Algorithm `qdfsa_traversal`, instrumented. Per input symbol: line 4 (`k`), lines 6–7 (`2k`),
line 8 (`1`), line 10 (`k - 1`), line 12 (`k`); then line 1 (`1`) and lines 14–15 (`k`). -/
def traverseT [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) : Bool × ℕ :=
  let r := w.foldl (fun (qc : (∀ i, Q i) × ℕ) a =>
    (M.delta qc.1 a, qc.2 + k + 2 * k + 1 + (k - 1) + k)) (M.start, 1)
  (decide (∃ i, r.1 i ∈ M.final i), r.2 + k)

private theorem foldl_cost (n₀ : ℕ) (q : ∀ i, Q i) (w : List α) :
    w.foldl (fun (qc : (∀ i, Q i) × ℕ) a =>
      (M.delta qc.1 a, qc.2 + k + 2 * k + 1 + (k - 1) + k)) (q, n₀) =
      (M.deltaStar q w, n₀ + 5 * k * w.length) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  induction w generalizing q n₀ with
  | nil => simp
  | cons a w ih =>
    rw [List.foldl_cons, ih, deltaStar_cons, List.length_cons]
    congr 1
    rw [Nat.mul_succ]
    omega

/-- Algorithm `qdfsa_traversal` decides membership, in exactly `1 + 5kn + k` steps. -/
theorem traverseT_spec [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) :
    ((M.traverseT w).1 = true ↔ w ∈ M.language) ∧
      (M.traverseT w).2 = 1 + 5 * k * w.length + k := by
  refine ⟨by simp only [traverseT, foldl_cost, decide_eq_true_eq]; rfl, by
    simp [traverseT, foldl_cost]⟩

/-- The `O(kn)` bound. -/
theorem traverseT_cost_le [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) :
    (M.traverseT w).2 ≤ 6 * k * (w.length + 1) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  rw [(M.traverseT_spec w).2, Nat.mul_succ]
  nlinarith

end QDFA

/-! ### Algorithm `lcp` -/

section Lcp

variable {β : Type*} [DecidableEq β]

/-- The column-scanning loop of Algorithm `lcp` (lines 6–10) on `w :: ws`, instrumented: per
column, `|ws|` comparisons (line 8) and one concatenation (line 10). It returns as soon as some
word disagrees with `w` or runs out, so it never scans past the shortest word. -/
def lcpCols : List β → List (List β) → List β × ℕ
  | [], _ => ([], 0)
  | a :: w, ws =>
    if ws.all (fun v => decide (v.head? = some a)) then
      let r := lcpCols w (ws.map List.tail)
      (a :: r.1, r.2 + ws.length + 1)
    else ([], ws.length)

theorem prefix_lcpCols_iff (c w : List β) (ws : List (List β)) :
    c <+: (lcpCols w ws).1 ↔ c <+: w ∧ ∀ v ∈ ws, c <+: v := by
  induction w generalizing ws c with
  | nil =>
    simp only [lcpCols, List.prefix_nil]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ _ => List.nil_prefix⟩
    · exact fun h => h.1
  | cons a w ih =>
    simp only [lcpCols]
    split_ifs with h
    · rw [List.all_eq_true] at h
      have hv : ∀ v ∈ ws, v = a :: v.tail := fun v hv => by
        have := of_decide_eq_true (h v hv)
        cases v with
        | nil => simp at this
        | cons b v => simp at this; simp [this]
      cases c with
      | nil => simp
      | cons b c =>
        simp only [List.cons_prefix_cons, ih, List.mem_map]
        constructor
        · rintro ⟨rfl, hw, hws⟩
          refine ⟨⟨rfl, hw⟩, fun v hv' => ?_⟩
          rw [hv v hv', List.cons_prefix_cons]
          exact ⟨rfl, hws _ ⟨v, hv', rfl⟩⟩
        · rintro ⟨⟨rfl, hw⟩, hws⟩
          refine ⟨rfl, hw, ?_⟩
          rintro _ ⟨v, hv', rfl⟩
          have := hws v hv'
          rw [hv v hv', List.cons_prefix_cons] at this
          exact this.2
    · simp only [List.all_eq_true, not_forall] at h
      obtain ⟨v, hv, hne⟩ := h
      simp only [List.prefix_nil]
      constructor
      · rintro rfl; exact ⟨List.nil_prefix, fun _ _ => List.nil_prefix⟩
      · rintro ⟨hw, hws⟩
        cases c with
        | nil => rfl
        | cons b c =>
          exfalso
          rw [List.cons_prefix_cons] at hw
          obtain ⟨rfl, -⟩ := hw
          obtain ⟨t, ht⟩ := hws v hv
          exact hne (by rw [← ht]; simp)

omit [DecidableEq β] in
theorem eq_of_prefix_iff {x y : List β} (h : ∀ c, c <+: x ↔ c <+: y) : x = y :=
  ((h x).mp (List.prefix_refl x)).eq_of_length
    (le_antisymm ((h x).mp (List.prefix_refl x)).length_le
      ((h y).mpr (List.prefix_refl y)).length_le)

/-- Algorithm `lcp` is correct. -/
theorem lcpCols_eq_lcpK (w : List β) (ws : List (List β)) :
    (lcpCols w ws).1 = QSFST.lcpK (w :: ws) :=
  eq_of_prefix_iff fun c => by
    rw [prefix_lcpCols_iff, QSFST.prefix_lcpK_iff, List.forall_mem_cons]

/-- The loop of Algorithm `lcp` takes at most `(|p| + 1)·k` steps for `k = |ws| + 1` words with
result `p`. -/
theorem lcpCols_cost_le (w : List β) (ws : List (List β)) :
    (lcpCols w ws).2 ≤ ((lcpCols w ws).1.length + 1) * (ws.length + 1) := by
  induction w generalizing ws with
  | nil => simp [lcpCols]
  | cons a w ih =>
    simp only [lcpCols]
    split_ifs
    · have := ih (ws.map List.tail)
      simp only [List.length_map] at this
      simp only [List.length_cons]
      nlinarith
    · simp

/-- The whole Algorithm `lcp`, including the minimum-length computation (lines 1–4, `k - 1`
steps): at most `(|p| + 2)·k` steps, where `|p| ≤ min |wᵢ|`. -/
theorem lcp_algorithm_cost_le (w : List β) (ws : List (List β)) :
    ws.length + (lcpCols w ws).2 ≤ ((lcpCols w ws).1.length + 2) * (ws.length + 1) ∧
      ∀ v ∈ w :: ws, (lcpCols w ws).1.length ≤ v.length := by
  refine ⟨by have := lcpCols_cost_le w ws; nlinarith, fun v hv => ?_⟩
  rw [lcpCols_eq_lcpK]
  exact (((QSFST.prefix_lcpK_iff _ w ws).mp (List.prefix_refl _)) v hv).length_le

end Lcp

/-! ### Algorithm `qsfst_traversal` -/

namespace QSFST

universe u v w x

variable {α : Type u} {β : Type x} [DecidableEq β] {k : ℕ} [NeZero k] {Q : Fin k → Type v}
  {X : Type w} (M : QSFST α β k Q X)

/-- `λ(q, σ)` is the lcp of the defined `λᵢ(qⁱ, σ)`. -/
theorem olam_eq_lcpK (q : ∀ i, Q i) (a : α) :
    M.olam q a = match (List.finRange k).filterMap (fun i => M.lam i (q i) a) with
      | [] => none
      | l :: ls => some (lcpK (l :: ls)) := by
  have hspec : OIsLcp (⋃ i, {x | M.lam i (q i) a = some x}) (M.olam q a) := by
    refine iterEtaX_olcp _ _ fun i => ?_
    rcases h : M.lam i (q i) a with _ | x
    · simp [OIsLcp]
    · refine ⟨⟨x, by simp⟩, fun c => ?_⟩
      simp
  have hU : (⋃ i, {x | M.lam i (q i) a = some x}) =
      {x | x ∈ (List.finRange k).filterMap (fun i => M.lam i (q i) a)} := by
    ext x; simp
  rw [hU] at hspec
  split
  · next h =>
    rw [h] at hspec
    exact hspec.eq_none_iff.mpr (by simp)
  · next l ls h =>
    rw [h] at hspec
    rcases hm : M.olam q a with _ | m
    · rw [hm] at hspec
      exact absurd hspec (Set.nonempty_iff_ne_empty.mp ⟨l, by simp⟩)
    · rw [hm] at hspec
      congr 1
      refine eq_of_prefix_iff fun c => ?_
      rw [← hspec.2 c, prefix_lcpK_iff]
      simp

/-- Lines 3–24 of Algorithm `qsfst_traversal`, instrumented: returns whether every symbol had a
transition, the output emitted, the final state, and the number of steps. Per symbol: line 4
(`1`), lines 5–10 (`3k`), line 11 (`1`), line 13 (Algorithm `lcp` on the defined `lⱼ`, plus `1`
for the concatenation), line 14 (`1`), line 17 (`k - 1`), line 20 (`k`). -/
def runT : (∀ i, Q i) → List α → Bool × List β × (∀ i, Q i) × ℕ
  | q, [] => (true, [], q, 0)
  | q, a :: w =>
    match (List.finRange k).filterMap (fun i => M.lam i (q i) a) with
    | [] => (false, [], q, 1 + 3 * k + 1)
    | l :: ls =>
      let p := lcpCols l ls
      let r := runT (M.delta q a) w
      (r.1, p.1 ++ r.2.1, r.2.2.1,
        r.2.2.2 + (1 + 3 * k + 1) + (ls.length + p.2 + 1) + 1 + (k - 1) + k)

theorem runT_some (q : ∀ i, Q i) (w : List α) (o : List β) (h : M.lamStar q w = some o) :
    (M.runT q w).1 = true ∧ (M.runT q w).2.1 = o ∧ (M.runT q w).2.2.1 = M.deltaStar q w := by
  induction w generalizing q o with
  | nil => cases h; exact ⟨rfl, rfl, rfl⟩
  | cons a w ih =>
    simp only [lamStar, olam_eq_lcpK] at h
    simp only [runT]
    split
    · next hl => rw [hl] at h; simp at h
    · next l ls hl =>
      rw [hl] at h
      simp only [Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨o', ho', rfl⟩ := h
      obtain ⟨h₁, h₂, h₃⟩ := ih _ _ ho'
      exact ⟨h₁, by rw [h₂, lcpCols_eq_lcpK], h₃⟩

theorem runT_none (q : ∀ i, Q i) (w : List α) (h : M.lamStar q w = none) :
    (M.runT q w).1 = false := by
  induction w generalizing q with
  | nil => simp [lamStar] at h
  | cons a w ih =>
    simp only [lamStar, olam_eq_lcpK] at h
    simp only [runT]
    split
    · rfl
    · next l ls hl =>
      rw [hl] at h
      simp only [Option.bind_some, Option.map_eq_none_iff] at h
      exact ih _ h

/-- Each symbol costs at most `11k` plus `k` per emitted output symbol. -/
theorem runT_cost_le (q : ∀ i, Q i) (w : List α) :
    (M.runT q w).2.2.2 ≤ 11 * k * w.length + k * (M.runT q w).2.1.length := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  induction w generalizing q with
  | nil => simp [runT]
  | cons a w ih =>
    simp only [runT]
    split
    · simp only [List.length_cons, List.length_nil]
      nlinarith
    · next l ls hl =>
      have hlen : ls.length + 1 ≤ k := by
        have := List.length_filterMap_le (fun i => M.lam i (q i) a) (List.finRange k)
        rw [hl, List.length_finRange] at this
        simpa using this
      have hp := lcpCols_cost_le l ls
      have ihq := ih (M.delta q a)
      have hmul : ((lcpCols l ls).1.length + 1) * (ls.length + 1) ≤
          ((lcpCols l ls).1.length + 1) * k := Nat.mul_le_mul_left _ hlen
      have hk1 : k - 1 ≤ k := Nat.sub_le k 1
      simp only [List.length_append, List.length_cons]
      nlinarith

/-- Algorithm `qsfst_traversal`, instrumented: lines 1–2 (`2`), lines 3–24 (`runT`),
lines 25–27 (`k`), and the final concatenation (`1`). -/
def traverseT [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) : Option (List β) × ℕ :=
  let r := M.runT M.start w
  if r.1 then
    match (List.finRange k).find? (fun i => decide (r.2.2.1 i ∈ M.final i)) with
    | some i => (some (r.2.1 ++ M.psi i (r.2.2.1 i)), r.2.2.2 + 2 + k + 1)
    | none => (none, r.2.2.2 + 2 + k)
  else (none, r.2.2.2 + 2)

/-- The instrumented algorithm computes `traverse`. -/
theorem traverseT_eq [∀ i, DecidablePred (· ∈ M.final i)] (w : List α) :
    (M.traverseT w).1 = M.traverse w := by
  simp only [traverseT, traverse]
  rcases h : M.lamStar M.start w with _ | o
  · rw [runT_none M _ _ h]; rfl
  · obtain ⟨h₁, h₂, h₃⟩ := runT_some M _ _ _ h
    rw [h₁, h₂, h₃, Option.bind_some]
    simp only [↓reduceIte]
    split <;> simp_all

/-- The `O(k(n + m))` bound: a successful translation `v` of `w` takes at most
`12k(|w| + 1) + k|v|` steps. -/
theorem traverseT_cost_le [∀ i, DecidablePred (· ∈ M.final i)] {w : List α} {v : List β}
    (h : (M.traverseT w).1 = some v) :
    (M.traverseT w).2 ≤ 12 * k * (w.length + 1) + k * v.length := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hc := M.runT_cost_le M.start w
  simp only [traverseT] at h ⊢
  by_cases hr : (M.runT M.start w).1 = true
  · simp only [hr, ↓reduceIte] at h ⊢
    rcases hf : (List.finRange k).find?
        (fun i => decide ((M.runT M.start w).2.2.1 i ∈ M.final i)) with _ | i
    · rw [hf] at h; simp at h
    · rw [hf] at h
      obtain rfl : (M.runT M.start w).2.1 ++ M.psi i ((M.runT M.start w).2.2.1 i) = v :=
        Option.some.inj h
      show (M.runT M.start w).2.2.2 + 2 + k + 1 ≤ _
      simp only [List.length_append]
      nlinarith
  · simp only [Bool.not_eq_true] at hr
    simp [hr] at h

end QSFST

end Sqdfsa
