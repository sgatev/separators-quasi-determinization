import Sqdfsa.Complexity.QuasiDet

/-!
# Per-component quasi-determinization

Algorithm `quasi_det_sfsa` explores the *global* states of `𝒜'`, and there are as many of
them as states of the subset-construction DFA (`quasiDetIterations_eq_subset`). The tables of
`𝒜'`, however, are indexed by *component* quasi-states and separator states only. This file
builds them by exploring each component separately:

* `compClosure A part i` (`U_i`) is the least set of quasi-states of component `i` that contains
  `sⁱ` and is closed under `τ_i(·, σ)` for every `σ ∈ Σ` and `η_i(·, x)` for **every** separator
  state `x ⊆ X`, not only for those produced by reachable global states.
* `perComponent A part` (`𝒜''`) is the QDFA with the tables of `𝒜'` restricted to the `U_i`.

Results:
* `deltaStar_mem_compClosure`: every reachable global state has its `i`-th component in `U_i`;
  hence `𝒜''` behaves like `𝒜'` (`perComponent_deltaStar`) and recognizes `𝓛_A`
  (`perComponent_language`).
* `ncard_compClosure_le`: `|U_i| ≤ 2^{|Q_i| + |X|}`.
* `perComponent_iterations`: a worklist exploration of component `i` processes each element of
  `U_i` exactly once.
* `perComponentCost_le`: in the thesis' cost model, the construction takes
  `O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ 2^{|Q_i|})` time, independently of the size of the
  subset-construction DFA.
* `blowup_perComponent`: on `blowup k`, every `U_i` has at most `4` elements, while
  Algorithm `quasi_det_sfsa` needs at least `2^k` iterations.
-/

set_option linter.unusedSectionVars false

namespace Sqdfsa

namespace FSA

variable {α Q : Type*} {k : ℕ} [NeZero k] {A : FSA α Q} {part : Q → Option (Fin k)}

variable (A part) in
/-- One step of the exploration of component `i`: apply `τ_i` for a symbol, or `η_i` for a
separator state. -/
def compStep (i : Fin k) (P : QuasiState part i) : α ⊕ SepState part → QuasiState part i
  | .inl a => (A.quasiDet part).tau i P a
  | .inr x => (A.quasiDet part).eta i P x

variable (A part) in
/-- `U_i`: the quasi-states of component `i` reachable from `sⁱ` by `τ_i` and `η_i`. -/
def compClosure (i : Fin k) : Set (QuasiState part i) :=
  reachable (A.compStep part i) ((A.quasiDet part).start i)

/-- Every reachable global state has its `i`-th component in `U_i`. -/
theorem deltaStar_mem_compClosure (w : List α) (i : Fin k) :
    (A.quasiDet part).deltaStar (A.quasiDet part).start w i ∈ A.compClosure part i := by
  induction w using List.reverseRecOn with
  | nil => exact start_mem_reachable
  | append_singleton w a ih =>
    rw [QDFA.deltaStar_append_singleton]
    exact mem_reachable_step (mem_reachable_step ih (.inl a))
      (.inr ((A.quasiDet part).deltaX ((A.quasiDet part).deltaStar (A.quasiDet part).start w) a))

variable (A part) in
/-- `𝒜''`: the tables of `𝒜'` restricted to the sets `U_i`. -/
def perComponent : QDFA α k (fun i => A.compClosure part i) (SepState part) where
  start i := ⟨(A.quasiDet part).start i, start_mem_reachable⟩
  final i := {P | P.1 ∈ (A.quasiDet part).final i}
  tau i P a := ⟨(A.quasiDet part).tau i P.1 a, mem_reachable_step P.2 (.inl a)⟩
  rho i P := (A.quasiDet part).rho i P.1
  eta i P x := ⟨(A.quasiDet part).eta i P.1 x, mem_reachable_step P.2 (.inr x)⟩
  etaX := (A.quasiDet part).etaX

theorem perComponent_deltaStar_from (q : ∀ i, A.compClosure part i) (w : List α) (i : Fin k) :
    ((A.perComponent part).deltaStar q w i).1 =
      (A.quasiDet part).deltaStar (fun i => (q i).1) w i := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    rw [QDFA.deltaStar_cons, QDFA.deltaStar_cons, ih]
    rfl

/-- `𝒜''` computes the same states as `𝒜'`. -/
theorem perComponent_deltaStar (w : List α) (i : Fin k) :
    ((A.perComponent part).deltaStar (A.perComponent part).start w i).1 =
      (A.quasiDet part).deltaStar (A.quasiDet part).start w i :=
  perComponent_deltaStar_from _ w i

/-- `𝒜''` recognizes the language of `A`. -/
theorem perComponent_language (hA : A.IsSeparator part) :
    (A.perComponent part).language = A.language := by
  rw [← quasiDet_language hA]
  ext w
  change (∃ i, ((A.perComponent part).deltaStar (A.perComponent part).start w i).1 ∈
      (A.quasiDet part).final i) ↔
    ∃ i, (A.quasiDet part).deltaStar (A.quasiDet part).start w i ∈ (A.quasiDet part).final i
  simp only [perComponent_deltaStar]

/-- `|𝒞(Q_i)| = |Q_i| + |X|`. -/
theorem ncard_comp [Finite Q] (i : Fin k) :
    (comp part i).ncard = {q | part q = some i}.ncard + (sepX part).ncard := by
  have : comp part i = {q | part q = some i} ∪ sepX part := by
    ext q; simp [comp, sepX, or_comm]
  rw [this, Set.ncard_union_eq]
  rw [Set.disjoint_left]
  intro q h₁ h₂
  simp only [Set.mem_ofPred_eq, sepX] at h₁ h₂
  rw [h₁] at h₂; cases h₂

/-- `|U_i| ≤ 2^{|Q_i| + |X|}`. -/
theorem ncard_compClosure_le [Finite Q] (i : Fin k) :
    (A.compClosure part i).ncard ≤ 2 ^ ({q | part q = some i}.ncard + (sepX part).ncard) := by
  rw [← ncard_comp, ← Nat.card_coe_set_eq]
  calc Nat.card (A.compClosure part i) ≤ Nat.card (QuasiState part i) :=
        Finite.card_subtype_le _
    _ = 2 ^ Nat.card (comp part i) := by
      have := Fintype.ofFinite Q
      classical
      rw [show Nat.card (QuasiState part i) = Nat.card (𝒫 (comp part i)) from rfl,
        Nat.card_congr (Equiv.Set.powerset _), Nat.card_eq_fintype_card, Fintype.card_set,
        ← Nat.card_eq_fintype_card]

/-- A worklist exploration of component `i` processes each element of `U_i` exactly once. -/
theorem perComponent_iterations [Finite Q] (i : Fin k) :
    ∃ m, ∀ N ≥ m, ∑ n ∈ Finset.range N,
      (reachR (A.compStep part i) ((A.quasiDet part).start i) (n + 1) \
        reachR (A.compStep part i) ((A.quasiDet part).start i) n).ncard =
      (A.compClosure part i).ncard :=
  iterations_eq_ncard_reachable (Set.toFinite _)

/-- The cost of the per-component construction in the thesis' model, where set operations cost
`|Q|`. For each component: initialization (`|Q|`), and for each of its `Iᵢ` processed
quasi-states, the final-state test and `ρ_i` (`2|Q|`), plus `|Σ|` applications of `τ_i` and
`2^{|X|}` applications of `η_i`, each followed by a worklist insertion (`2|Q|` each). Finally,
the table of `η_x` has `4^{|X|}` entries (unions, `|Q|` each). -/
def perComponentCost (nS nX nQ : ℕ) (I : Fin k → ℕ) : ℕ :=
  ∑ i, (nQ + I i * (2 * nQ + (nS + 2 ^ nX) * (2 * nQ))) + 4 ^ nX * nQ

omit [NeZero k] in
theorem perComponentCost_le_of [NeZero k] (nS nX nQ : ℕ) (b I : Fin k → ℕ)
    (hI : ∀ i, I i ≤ 2 ^ (b i + nX)) :
    perComponentCost nS nX nQ I ≤ 3 * (nS + 2 ^ nX + 1) * nQ * 2 ^ nX * ∑ i, 2 ^ b i := by
  set a := 2 ^ nX with ha
  have ha1 : 1 ≤ a := Nat.one_le_two_pow
  set c := 2 * nQ + (nS + a) * (2 * nQ) with hc
  have hS : 1 ≤ ∑ i, 2 ^ b i :=
    le_trans Nat.one_le_two_pow (Finset.single_le_sum (fun i _ => Nat.zero_le (2 ^ b i))
      (Finset.mem_univ (0 : Fin k)))
  have hterm : ∀ i, nQ + I i * c ≤ (nQ + a * c) * 2 ^ b i := fun i => by
    have he : 1 ≤ 2 ^ b i := Nat.one_le_two_pow
    have hIi : I i ≤ a * 2 ^ b i := by rw [ha, ← pow_add, add_comm]; exact hI i
    have h1 : I i * c ≤ a * 2 ^ b i * c := Nat.mul_le_mul_right _ hIi
    nlinarith
  have hsum : ∑ i, (nQ + I i * c) ≤ (nQ + a * c) * ∑ i, 2 ^ b i := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hterm i
  have h4 : 4 ^ nX = a * a := by rw [ha, ← mul_pow]; norm_num
  unfold perComponentCost
  rw [← ha, ← hc, h4]
  set S := ∑ i, 2 ^ b i
  have : a * a * nQ ≤ a * a * nQ * S := Nat.le_mul_of_pos_right _ hS
  have : (nQ + a * c) * S ≤ (nQ + a * c) * S := le_rfl
  rw [hc] at hsum ⊢
  nlinarith [Nat.zero_le (a * nQ * S), Nat.zero_le (a * a * nQ * S), Nat.zero_le (nS * a * nQ * S),
    Nat.zero_le (nQ * S), Nat.mul_le_mul_right (nQ * S) ha1]

/-- The per-component construction takes `O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ 2^{|Q_i|})` time. -/
theorem perComponentCost_le [Finite Q] :
    perComponentCost (Nat.card α) (sepX part).ncard (Nat.card Q)
        (fun i => (A.compClosure part i).ncard) ≤
      3 * (Nat.card α + 2 ^ (sepX part).ncard + 1) * Nat.card Q * 2 ^ (sepX part).ncard *
        ∑ i, 2 ^ {q | part q = some i}.ncard :=
  perComponentCost_le_of _ _ _ _ _ fun i => ncard_compClosure_le i

/-- On `blowup k`, the per-component construction explores at most `4` quasi-states per
component, whereas Algorithm `quasi_det_sfsa` needs at least `2^k` iterations. -/
theorem blowup_perComponent (k : ℕ) [NeZero k] :
    (∀ i, ((blowup k).compClosure id i).ncard ≤ 4) ∧
      2 ^ k ≤ quasiDetIterations (blowup k) id ∧
      ((blowup k).perComponent id).language = (blowup k).language := by
  refine ⟨fun i => ?_, blowup_iterations k, perComponent_language (blowup_isSeparator k)⟩
  have := ncard_compClosure_le (A := blowup k) (part := id) i
  rwa [blowup_block, blowup_sepX] at this

end FSA

end Sqdfsa
