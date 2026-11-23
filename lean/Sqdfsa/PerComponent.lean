import Sqdfsa.Complexity.QuasiDet

/-!
# Per-component quasi-determinization (Algorithm `quasi_det_sfsa_components`)

Algorithm `quasi_det_sfsa` explores the *global* states of `𝒜'`, and there are as many of
them as states of the subset-construction DFA (`quasiDetIterations_eq_subset`). The tables of
`𝒜'`, however, are indexed by *component* quasi-states and separator states only. The
per-component algorithm (`impl/eager_quasi_determinize.h`) explores each component separately:

* `compClosure A part i` (`U_i`) is the closure of `sⁱ` under `P ↦ η_i(τ_i(P, σ), x)` for every
  `σ ∈ Σ` and **every** separator state `x ⊆ X`, not only those that reachable global states
  produce. These are the explored quasi-states.
* `tauImage A part i` (`T_i`) is the set of results of `τ_i` on `U_i`; `η_i` is tabulated on it.
* `perComponent A part` (`𝒜''`) has the quasi-states `U_i ∪ T_i`, `τ_i` on `U_i`, `η_i` on `T_i`.

Results:
* `deltaStar_mem_compClosure`, `perComponent_deltaStar`, `perComponent_language`: `𝒜''` computes
  the same states as `𝒜'` and recognizes `𝓛_A`.
* `ncard_quasiStates_le`: `|U_i|, |T_i|, |U_i ∪ T_i| ≤ 2^{|Q_i| + |X|}`.
* `perComponent_iterations`: the worklist processes each element of `U_i` exactly once.
* `perComponentCost_le`: in the thesis' cost model, the construction takes
  `O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ 2^{|Q_i|})` time, independently of the DFA.
* `blowup_perComponent`: on `blowup k`, every component of `𝒜''` has at most `4`
  quasi-states, while Algorithm `quasi_det_sfsa` needs at least `2^k` iterations.
-/

set_option linter.unusedSectionVars false

namespace Sqdfsa

namespace FSA

variable {α Q : Type*} {k : ℕ} [NeZero k] {A : FSA α Q} {part : Q → Option (Fin k)}

variable (A part) in
/-- One step of the exploration of component `i`: `P ↦ η_i(τ_i(P, σ), x)`. -/
def compStep (i : Fin k) (P : QuasiState part i) (b : α × SepState part) : QuasiState part i :=
  (A.quasiDet part).eta i ((A.quasiDet part).tau i P b.1) b.2

variable (A part) in
/-- `U_i`: the quasi-states of component `i` reachable from `sⁱ` by `P ↦ η_i(τ_i(P, σ), x)`
for `σ ∈ Σ` and `x ⊆ X`. These are the quasi-states that the per-component algorithm
explores. -/
def compClosure (i : Fin k) : Set (QuasiState part i) :=
  reachable (A.compStep part i) ((A.quasiDet part).start i)

variable (A part) in
/-- `T_i`: the results of `τ_i` on `U_i`, i.e. the quasi-states on which `η_i` is tabulated. -/
def tauImage (i : Fin k) : Set (QuasiState part i) :=
  {t | ∃ P ∈ A.compClosure part i, ∃ a, t = (A.quasiDet part).tau i P a}

variable (A part) in
/-- The quasi-states of component `i` of `𝒜''`: `U_i ∪ T_i`. -/
def compStates (i : Fin k) : Set (QuasiState part i) := A.compClosure part i ∪ A.tauImage part i

theorem eta_mem_compClosure {i : Fin k} {t : QuasiState part i} (ht : t ∈ A.tauImage part i)
    (x : SepState part) : (A.quasiDet part).eta i t x ∈ A.compClosure part i := by
  obtain ⟨P, hP, a, rfl⟩ := ht
  exact mem_reachable_step hP (a, x)

/-- Every reachable global state has its `i`-th component in `U_i`. -/
theorem deltaStar_mem_compClosure (w : List α) (i : Fin k) :
    (A.quasiDet part).deltaStar (A.quasiDet part).start w i ∈ A.compClosure part i := by
  induction w using List.reverseRecOn with
  | nil => exact start_mem_reachable
  | append_singleton w a ih =>
    rw [QDFA.deltaStar_append_singleton]
    exact mem_reachable_step ih
      (a, (A.quasiDet part).deltaX ((A.quasiDet part).deltaStar (A.quasiDet part).start w) a)

variable (A part) in
/-- `𝒜''`: the tables of `𝒜'` restricted as in the per-component algorithm: `τ_i` on `U_i`,
`η_i` on `T_i`, final quasi-states in `U_i`. The thesis' tables are partial; since Lean
structures need total functions, the entries outside these domains are filled with a
placeholder (the argument itself). They are never used (`perComponent_delta`). -/
noncomputable def perComponent : QDFA α k (fun i => A.compStates part i) (SepState part) where
  start i := ⟨(A.quasiDet part).start i, Or.inl start_mem_reachable⟩
  final i := {P | P.1 ∈ A.compClosure part i ∧ P.1 ∈ (A.quasiDet part).final i}
  tau i P a := open Classical in
    if h : P.1 ∈ A.compClosure part i then
      ⟨(A.quasiDet part).tau i P.1 a, Or.inr ⟨P.1, h, a, rfl⟩⟩
    else P
  rho i P := (A.quasiDet part).rho i P.1
  eta i P x := open Classical in
    if h : P.1 ∈ A.tauImage part i then
      ⟨(A.quasiDet part).eta i P.1 x, Or.inl (eta_mem_compClosure h x)⟩
    else P
  etaX := (A.quasiDet part).etaX

theorem perComponent_tau {i : Fin k} (P : A.compStates part i) (h : P.1 ∈ A.compClosure part i)
    (a : α) : ((A.perComponent part).tau i P a).1 = (A.quasiDet part).tau i P.1 a := by
  simp [perComponent, h]

theorem perComponent_eta {i : Fin k} (P : A.compStates part i) (h : P.1 ∈ A.tauImage part i)
    (x : SepState part) : ((A.perComponent part).eta i P x).1 = (A.quasiDet part).eta i P.1 x := by
  simp [perComponent, h]

/-- On states whose components lie in `U_i`, `𝒜''` makes the same transitions as `𝒜'`, and the
results lie in `U_i` again. -/
theorem perComponent_delta (q : ∀ i, A.compStates part i)
    (hq : ∀ i, (q i).1 ∈ A.compClosure part i) (a : α) (i : Fin k) :
    ((A.perComponent part).delta q a i).1 = (A.quasiDet part).delta (fun i => (q i).1) a i ∧
      ((A.perComponent part).delta q a i).1 ∈ A.compClosure part i := by
  have hX : (A.perComponent part).deltaX q a = (A.quasiDet part).deltaX (fun i => (q i).1) a := by
    show iterEtaX (A.quasiDet part).etaX
        (fun j => (A.quasiDet part).rho j ((A.perComponent part).tau j (q j) a).1) = _
    simp only [perComponent_tau _ (hq _)]
    rfl
  have hT : ((A.perComponent part).tau i (q i) a).1 ∈ A.tauImage part i := by
    rw [perComponent_tau _ (hq i)]; exact ⟨_, hq i, a, rfl⟩
  have key : ((A.perComponent part).delta q a i).1 =
      (A.quasiDet part).delta (fun i => (q i).1) a i := by
    show ((A.perComponent part).eta i ((A.perComponent part).tau i (q i) a)
      ((A.perComponent part).deltaX q a)).1 = _
    rw [perComponent_eta _ hT, perComponent_tau _ (hq i), hX]
    rfl
  exact ⟨key, key ▸ mem_reachable_step (hq i) (a, _)⟩

theorem perComponent_deltaStar_from (q : ∀ i, A.compStates part i)
    (hq : ∀ i, (q i).1 ∈ A.compClosure part i) (w : List α) :
    (∀ i, ((A.perComponent part).deltaStar q w i).1 =
      (A.quasiDet part).deltaStar (fun i => (q i).1) w i) ∧
    ∀ i, ((A.perComponent part).deltaStar q w i).1 ∈ A.compClosure part i := by
  induction w generalizing q with
  | nil => exact ⟨fun _ => rfl, hq⟩
  | cons a w ih =>
    have h := perComponent_delta q hq a
    obtain ⟨ih₁, ih₂⟩ := ih ((A.perComponent part).delta q a) fun i => (h i).2
    refine ⟨fun i => ?_, ih₂⟩
    rw [QDFA.deltaStar_cons, QDFA.deltaStar_cons, ih₁]
    congr 1
    funext j
    exact (h j).1

/-- `𝒜''` computes the same states as `𝒜'`. -/
theorem perComponent_deltaStar (w : List α) (i : Fin k) :
    ((A.perComponent part).deltaStar (A.perComponent part).start w i).1 =
      (A.quasiDet part).deltaStar (A.quasiDet part).start w i :=
  (perComponent_deltaStar_from _ (fun _ => start_mem_reachable) w).1 i

/-- `𝒜''` recognizes the language of `A`. -/
theorem perComponent_language (hA : A.IsSeparator part) :
    (A.perComponent part).language = A.language := by
  rw [← quasiDet_language hA]
  ext w
  change (∃ i, ((A.perComponent part).deltaStar (A.perComponent part).start w i).1 ∈
        A.compClosure part i ∧
      ((A.perComponent part).deltaStar (A.perComponent part).start w i).1 ∈
        (A.quasiDet part).final i) ↔
    ∃ i, (A.quasiDet part).deltaStar (A.quasiDet part).start w i ∈ (A.quasiDet part).final i
  simp only [perComponent_deltaStar, deltaStar_mem_compClosure, true_and]

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

/-- Any set of quasi-states of component `i`, in particular `U_i`, `T_i` and `U_i ∪ T_i`, has at
most `2^{|Q_i| + |X|}` elements. -/
theorem ncard_quasiStates_le [Finite Q] (i : Fin k) (U : Set (QuasiState part i)) :
    U.ncard ≤ 2 ^ ({q | part q = some i}.ncard + (sepX part).ncard) := by
  rw [← ncard_comp, ← Nat.card_coe_set_eq]
  calc Nat.card U ≤ Nat.card (QuasiState part i) := Finite.card_subtype_le _
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
`|Q|`. For each component: initialization (`|Q|`); for each of the `Iᵢ` explored quasi-states,
the final-state test and the worklist bookkeeping (`2|Q|`) and `|Σ|` applications of `τ_i` and
`ρ_i` (`2|Q|` each); for each of the `Jᵢ` distinct results of `τ_i`, `2^{|X|}` applications of
`η_i`, each with a worklist insertion (`2|Q|` each). Finally, the table of `η_x` has `4^{|X|}`
entries (unions, `|Q|` each). -/
def perComponentCost (nS nX nQ : ℕ) (I J : Fin k → ℕ) : ℕ :=
  ∑ i, (nQ + I i * (2 * nQ + nS * (2 * nQ)) + J i * (2 ^ nX * (2 * nQ))) + 4 ^ nX * nQ

omit [NeZero k] in
theorem perComponentCost_le_of [NeZero k] (nS nX nQ : ℕ) (b I J : Fin k → ℕ)
    (hI : ∀ i, I i ≤ 2 ^ (b i + nX)) (hJ : ∀ i, J i ≤ 2 ^ (b i + nX)) :
    perComponentCost nS nX nQ I J ≤ 3 * (nS + 2 ^ nX + 1) * nQ * 2 ^ nX * ∑ i, 2 ^ b i := by
  set a := 2 ^ nX with ha
  have ha1 : 1 ≤ a := Nat.one_le_two_pow
  have hS : 1 ≤ ∑ i, 2 ^ b i :=
    le_trans Nat.one_le_two_pow (Finset.single_le_sum (fun i _ => Nat.zero_le (2 ^ b i))
      (Finset.mem_univ (0 : Fin k)))
  have hterm : ∀ i, nQ + I i * (2 * nQ + nS * (2 * nQ)) + J i * (a * (2 * nQ)) ≤
      (nQ + a * (2 * nQ + nS * (2 * nQ)) + a * (a * (2 * nQ))) * 2 ^ b i := fun i => by
    have he : 1 ≤ 2 ^ b i := Nat.one_le_two_pow
    have hIi : I i ≤ a * 2 ^ b i := by rw [ha, ← pow_add, add_comm]; exact hI i
    have hJi : J i ≤ a * 2 ^ b i := by rw [ha, ← pow_add, add_comm]; exact hJ i
    have h1 := Nat.mul_le_mul_right (2 * nQ + nS * (2 * nQ)) hIi
    have h2 := Nat.mul_le_mul_right (a * (2 * nQ)) hJi
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← Finset.mul_sum] at hsum
  have h4 : 4 ^ nX = a * a := by rw [ha, ← mul_pow]; norm_num
  unfold perComponentCost
  rw [← ha, h4]
  set S := ∑ i, 2 ^ b i
  have : a * a * nQ ≤ a * a * nQ * S := Nat.le_mul_of_pos_right _ hS
  nlinarith [Nat.zero_le (a * nQ * S), Nat.zero_le (a * a * nQ * S), Nat.zero_le (nS * a * nQ * S),
    Nat.zero_le (nQ * S), Nat.mul_le_mul_right (nQ * S) ha1]

/-- The per-component construction takes `O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ 2^{|Q_i|})` time. -/
theorem perComponentCost_le [Finite Q] :
    perComponentCost (Nat.card α) (sepX part).ncard (Nat.card Q)
        (fun i => (A.compClosure part i).ncard) (fun i => (A.tauImage part i).ncard) ≤
      3 * (Nat.card α + 2 ^ (sepX part).ncard + 1) * Nat.card Q * 2 ^ (sepX part).ncard *
        ∑ i, 2 ^ {q | part q = some i}.ncard :=
  perComponentCost_le_of _ _ _ _ _ _ (fun i => ncard_quasiStates_le i _)
    (fun i => ncard_quasiStates_le i _)

/-- On `blowup k`, every component of `𝒜''` has at most `4` quasi-states, whereas Algorithm
`quasi_det_sfsa` needs at least `2^k` iterations. -/
theorem blowup_perComponent (k : ℕ) [NeZero k] :
    (∀ i, ((blowup k).compStates id i).ncard ≤ 4) ∧
      2 ^ k ≤ quasiDetIterations (blowup k) id ∧
      ((blowup k).perComponent id).language = (blowup k).language := by
  refine ⟨fun i => ?_, blowup_iterations k, perComponent_language (blowup_isSeparator k)⟩
  have := ncard_quasiStates_le (part := (id : Option (Fin k) → Option (Fin k))) i
    ((blowup k).compStates id i)
  rwa [blowup_block, blowup_sepX] at this

end FSA

end Sqdfsa
