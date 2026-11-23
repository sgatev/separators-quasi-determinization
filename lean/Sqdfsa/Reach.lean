import Mathlib

/-!
# The reachable-state sequence `R^{(n)}` of the incremental constructions

Both quasi-determinization (§3.5) and quasi-subsequentialization (§4.4) build their
devices incrementally: `R^{(0)} = ∅`, `R^{(1)} = {s}`,
`R^{(n+1)} = R^{(n)} ∪ {δ(q, σ) | q ∈ R_n, σ ∈ Σ}` with `R_n = R^{(n)} \ R^{(n-1)}`.
This file treats an arbitrary deterministic step function `δ`.
-/

namespace Sqdfsa

variable {S α : Type*} (δ : S → α → S) (s : S)

/-- `(R^{(n)}, R^{(n-1)})`. -/
def reachSeq : ℕ → Set S × Set S
  | 0 => (∅, ∅)
  | 1 => ({s}, ∅)
  | n + 2 =>
    ((reachSeq (n + 1)).1 ∪ {p | ∃ q ∈ (reachSeq (n + 1)).1 \ (reachSeq (n + 1)).2, ∃ a,
      p = δ q a}, (reachSeq (n + 1)).1)

/-- `R^{(n)}`. -/
def reachR (n : ℕ) : Set S := (reachSeq δ s n).1

/-- All states reachable from `s`. -/
def reachable : Set S := {p | ∃ w : List α, p = w.foldl δ s}

variable {δ s}

theorem reachSeq_snd (n : ℕ) : (reachSeq δ s (n + 1)).2 = reachR δ s n := by
  cases n <;> rfl

theorem reachR_succ_succ (n : ℕ) :
    reachR δ s (n + 2) = reachR δ s (n + 1) ∪
      {p | ∃ q ∈ reachR δ s (n + 1) \ reachR δ s n, ∃ a, p = δ q a} := by
  show (reachSeq δ s (n + 2)).1 = _
  rw [reachSeq, reachSeq_snd]; rfl

theorem reachR_mono : Monotone (reachR δ s) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases n with _ | n
  · exact Set.empty_subset _
  · rw [reachR_succ_succ]; exact Set.subset_union_left

/-- `R^{(n+1)}` consists exactly of the states reached by words of length at most `n`. -/
theorem reachR_succ_eq (n : ℕ) :
    reachR δ s (n + 1) = {p | ∃ w : List α, w.length ≤ n ∧ p = w.foldl δ s} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · ext p
    simp [reachR, reachSeq]
  have ihn := ih n (Nat.lt_succ_self n)
  ext p
  rw [reachR_succ_succ, Set.mem_union, ihn]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro (⟨w, hw, rfl⟩ | ⟨q, ⟨⟨w, hw, rfl⟩, -⟩, a, rfl⟩)
    · exact ⟨w, by omega, rfl⟩
    · exact ⟨w ++ [a], by simp; omega, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    rcases Nat.lt_or_eq_of_le hw with hw | hw
    · exact Or.inl ⟨w, by omega, rfl⟩
    obtain ⟨v, a, rfl⟩ : ∃ v a, w = v ++ [a] := by
      rcases List.eq_nil_or_concat w with h | ⟨v, a, h⟩
      · simp [h] at hw
      · exact ⟨v, a, by simpa using h⟩
    simp only [List.length_append, List.length_singleton] at hw
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hv : v.foldl δ s ∈ reachR δ s n
    · -- `v.foldl δ s` was already reached by a shorter word `v'`
      rcases n with _ | m
      · simp [reachR, reachSeq] at hv
      rw [ih m (by omega)] at hv
      obtain ⟨v', hv', hvv⟩ := hv
      refine Or.inl ⟨v' ++ [a], by simp; omega, ?_⟩
      rw [hvv]; simp
    · exact Or.inr ⟨_, ⟨⟨v, by omega, rfl⟩, hv⟩, a, rfl⟩

theorem reachR_succ_subset (n : ℕ) : reachR δ s (n + 1) ⊆ reachable δ s := by
  rw [reachR_succ_eq]
  rintro p ⟨w, -, rfl⟩
  exact ⟨w, rfl⟩

/-- Lemmas `quasidet_completion` / `quasisubseq_completion` (abstract form): if only finitely many
states are reachable, the sequence `R^{(n)}` stabilizes at the set of reachable states. -/
theorem reachR_stabilizes (hfin : (reachable δ s).Finite) :
    ∃ m, ∀ n ≥ m, reachR δ s n = reachR δ s (n + 1) ∧ reachR δ s n = reachable δ s := by
  have : Finite (reachable δ s) := hfin.to_subtype
  let g : ℕ →o Set (reachable δ s) :=
    ⟨fun n => Subtype.val ⁻¹' reachR δ s (n + 1), fun _ _ h =>
      Set.preimage_mono (reachR_mono (Nat.succ_le_succ h))⟩
  obtain ⟨m, hm⟩ := WellFoundedGT.monotone_chain_condition g
  have hR : ∀ n, reachR δ s (n + 1) = Subtype.val '' g n := fun n => by
    show _ = Subtype.val '' (Subtype.val ⁻¹' reachR δ s (n + 1))
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr (reachR_succ_subset n)]
  have hconst : ∀ n ≥ m, reachR δ s (n + 1) = reachR δ s (m + 1) := fun n hn => by
    rw [hR, hR, hm n hn]
  have hall : reachR δ s (m + 1) = reachable δ s := by
    refine (reachR_succ_subset m).antisymm ?_
    rintro p ⟨w, rfl⟩
    have hw : w.foldl δ s ∈ reachR δ s (w.length + 1) := by
      rw [reachR_succ_eq]; exact ⟨w, le_rfl, rfl⟩
    rcases le_total w.length m with h | h
    · exact reachR_mono (by omega) hw
    · rwa [hconst _ h] at hw
  refine ⟨m + 1, fun n hn => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [hconst n (by omega), hconst (n + 1) (by omega)]
  exact ⟨rfl, hall⟩

end Sqdfsa
