import Sqdfsa.QuasiDet
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Complexity of quasi-determinization (thesis §3.5, Algorithm `quasi_det_sfsa`)

The while loop of Algorithm `quasi_det_sfsa` extracts every state of `R` exactly once: a state is
added to `Next` only if it is not in `Visited`. The thesis' proposition `𝒜_c = 𝒜'` shows that
the loop processes the frontiers `R_n` in order. So the number of iterations is
`Σₙ |R_n| = |R|` (`sum_frontier_ncard`), the number of reachable states of `𝒜'`.

The thesis bounds this number by `2^{|X|}(1 + Σᵢ 2^{|Q_i|})`, from which it derives the runtime
`O(k|Σ||Q|2^{|X|}Σᵢ2^{|Q_i|})`. That bound counts entries of the per-component tables. The loop,
however, ranges over *global* states (tuples of quasi-states). We show:

* `quasiDetIterations_eq_subset`: the number of iterations **equals** the number of states of
  the Rabin–Scott subset-construction DFA (`A.toεNFA.toNFA.toDFA`, restricted to reachable
  states). This follows from the invariant `deltaStar_quasiDet`.
* `quasiDetIterations_le`: hence it is at most `2^{|Q|}`, and the cost under the thesis' own
  accounting is `O(k|Σ||Q|·D)`, where `D` is the size of the subset-construction DFA
  (`quasiDetCost_le`).
* `blowup`: a family of `k`-separated automata with `|X| = |Q_i| = 1` and `|Σ| = k`. Its loop runs
  at least `2^k` times. This refutes the iteration bound for every `k ≥ 5`
  (`thesis_iteration_bound_false`) and the runtime bound for every constant
  (`thesis_runtime_bound_false`).

The table sizes, and hence the space bound `Σᵢ 2^{|Q_i|+|X|}`, are unaffected
(`FSA.exists_quasiDet`). The time to *build* the tables is what the thesis underestimates.
-/

namespace Sqdfsa

/-! ### Iterations of the worklist loop -/

section Generic

variable {S α : Type*} {δ : S → α → S} {s : S}

/-- Processing the frontiers `R_0, …, R_{N-1}` takes `|R^{(N)}|` iterations. -/
theorem sum_frontier_ncard (hfin : (reachable δ s).Finite) (N : ℕ) :
    ∑ n ∈ Finset.range N, (reachR δ s (n + 1) \ reachR δ s n).ncard = (reachR δ s N).ncard := by
  induction N with
  | zero => simp [reachR, reachSeq]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, add_comm]
    exact Set.ncard_sdiff_add_ncard_of_subset (reachR_mono (Nat.le_succ N))
      (hfin.subset (reachR_succ_subset N))

/-- Eventually, the total number of processed states is the number of reachable states. -/
theorem iterations_eq_ncard_reachable (hfin : (reachable δ s).Finite) :
    ∃ m, ∀ N ≥ m, ∑ n ∈ Finset.range N, (reachR δ s (n + 1) \ reachR δ s n).ncard =
      (reachable δ s).ncard := by
  obtain ⟨m, hm⟩ := reachR_stabilizes hfin
  exact ⟨m, fun N hN => by rw [sum_frontier_ncard hfin, (hm N hN).2]⟩

end Generic

namespace FSA

variable {α Q : Type*} {k : ℕ} [NeZero k] {A : FSA α Q} {part : Q → Option (Fin k)}

variable (A part) in
/-- The number of iterations of the while loop of Algorithm `quasi_det_sfsa`. -/
noncomputable def quasiDetIterations : ℕ :=
  (reachable (A.quasiDet part).delta (A.quasiDet part).start).ncard

theorem quasiDetIterations_eq_frontier [Finite Q] :
    ∃ m, ∀ N ≥ m, ∑ n ∈ Finset.range N,
      (reachR (A.quasiDet part).delta (A.quasiDet part).start (n + 1) \
        reachR (A.quasiDet part).delta (A.quasiDet part).start n).ncard =
      quasiDetIterations A part :=
  iterations_eq_ncard_reachable (Set.toFinite _)

/-- `reach w` is the state reached by the subset-construction DFA on `w`. -/
theorem reach_eq_eval (w : List α) : A.reach w = A.toεNFA.toNFA.toDFA.eval w := by
  have : A.toεNFA.toNFA.toDFA.eval w = A.toεNFA.evalFrom A.start w := by
    rw [← εNFA.toNFA_evalFrom_match]; rfl
  rw [this]
  ext q
  rw [εNFA.mem_evalFrom_iff_exists]
  simp only [reach, Set.mem_ofPred_eq, εNFA.mem_evalFrom_iff_exists_path, star_iff_exists_path]

/-- The while loop runs exactly as many times as the subset-construction DFA has (reachable)
states. -/
theorem quasiDetIterations_eq_subset (hA : A.IsSeparator part) :
    quasiDetIterations A part = {S | ∃ w, S = A.toεNFA.toNFA.toDFA.eval w}.ncard := by
  have : Nonempty (Fin k) := ⟨0⟩
  let ψ : Set Q → ∀ i, QuasiState part i := fun R i => ⟨R ∩ comp part i, Set.inter_subset_right⟩
  have hψ : Function.Injective ψ := fun R R' h => by
    ext q
    obtain ⟨i, hi⟩ := exists_mem_comp (part := part) q
    have := congrArg Subtype.val (congrFun h i)
    simp only [ψ] at this
    constructor
    · intro hq; exact (this ▸ ⟨hq, hi⟩ : q ∈ R' ∩ comp part i).1
    · intro hq; exact (this.symm ▸ ⟨hq, hi⟩ : q ∈ R ∩ comp part i).1
  have hreach : reachable (A.quasiDet part).delta (A.quasiDet part).start =
      ψ '' {S | ∃ w, S = A.toεNFA.toNFA.toDFA.eval w} := by
    ext p
    have key : ∀ w, (A.quasiDet part).deltaStar (A.quasiDet part).start w = ψ (A.reach w) :=
      fun w => funext fun i => Subtype.ext (deltaStar_quasiDet hA w i)
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨A.reach w, ⟨w, reach_eq_eval w⟩, (key w).symm⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, by rw [← reach_eq_eval]; exact (key w).symm⟩
  rw [quasiDetIterations, hreach, Set.ncard_image_of_injective _ hψ]

/-- Corrected bound on the number of iterations: at most `2^{|Q|}`. -/
theorem quasiDetIterations_le [Finite Q] (hA : A.IsSeparator part) :
    quasiDetIterations A part ≤ 2 ^ Nat.card Q := by
  rw [quasiDetIterations_eq_subset hA]
  have := Fintype.ofFinite Q
  classical
  calc _ ≤ (Set.univ : Set (Set Q)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 2 ^ Nat.card Q := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_set, Nat.card_eq_fintype_card]

/-- The thesis' cost accounting for Algorithm `quasi_det_sfsa`, with `I` loop iterations and
set operations costing `|Q|`: lines 1–9 cost `|Q| + k|Q| + 2`; each iteration costs line 11
(`1`) and lines 13–15 (`k|Q|`), plus, per symbol, line 18 (`1`), lines 20–26 (`k|Q|`),
lines 28–29 (`(k - 1)|Q|`), lines 31–33 (`k|Q|`), and lines 35–37 (`k|Q|`). -/
def quasiDetCost (k nS nQ I : ℕ) : ℕ :=
  nQ + k * nQ + 2 + I * (1 + k * nQ + nS * (1 + k * nQ + (k - 1) * nQ + k * nQ + k * nQ))

/-- With the correct iteration count, the runtime is `O(k|Σ||Q|·D)`, where `D` is the number of
states of the subset-construction DFA. -/
theorem quasiDetCost_le (nS nQ : ℕ) (hA : A.IsSeparator part) :
    quasiDetCost k nS nQ (quasiDetIterations A part) ≤
      5 * k * (nS + 1) * (nQ + 1) * ({S | ∃ w, S = A.toεNFA.toNFA.toDFA.eval w}.ncard + 1) := by
  rw [← quasiDetIterations_eq_subset hA]
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  generalize quasiDetIterations A part = I
  unfold quasiDetCost
  have h1 : (k - 1) * nQ ≤ k * nQ := Nat.mul_le_mul_right _ (Nat.sub_le k 1)
  generalize (k - 1) * nQ = t at h1 ⊢
  nlinarith [Nat.zero_le (k * nQ), Nat.zero_le (nS * I), Nat.zero_le (k * nQ * nS * I),
    Nat.zero_le (k * nS), Nat.zero_le (k * nQ * I), Nat.zero_le (nQ * nS * I)]

/-! ### The counterexample family -/

/-- `blowup k`: a start state `x` (`none`) with `ε`-transitions to `k` states `q_j` (`some j`);
`q_j` loops on every letter except `j`. With `part = id` it is `k`-separated with
`X = {x}` and `Q_j = {q_j}`. After reading `w`, exactly the `q_j` with `j ∉ w` are alive, so
the subset construction reaches `2^k` different states. -/
def blowup (k : ℕ) : FSA (Fin k) (Option (Fin k)) where
  start := {none}
  final := ∅
  delta := {t | (∃ j, t = (none, none, some j)) ∨ ∃ j b, b ≠ j ∧ t = (some j, some b, some j)}

theorem blowup_isSeparator (k : ℕ) : (blowup k).IsSeparator id := by
  rintro q a q' i j (⟨j', h⟩ | ⟨j', b, -, h⟩) hi hj
  · simp only [Prod.mk.injEq] at h
    rw [h.1] at hi; simp at hi
  · simp only [Prod.mk.injEq] at h
    rw [h.1] at hi; rw [h.2.2] at hj
    simp only [id] at hi hj
    rw [← Option.some_injective _ hi, ← Option.some_injective _ hj]

theorem blowup_star_none {k : ℕ} {p q : Option (Fin k)} {w : List (Fin k)}
    (h : (blowup k).Star p w q) (hq : q = none) : p = none ∧ w = [] := by
  induction h with
  | refl => exact ⟨hq, rfl⟩
  | tail _ hd _ =>
    subst hq
    rcases hd with ⟨j, h⟩ | ⟨j, b, -, h⟩ <;> simp at h

theorem blowup_star_some {k : ℕ} {p q : Option (Fin k)} {w : List (Fin k)}
    (h : (blowup k).Star p w q) (j : Fin k) (hq : q = some j) :
    (p = none ∨ p = some j) ∧ j ∉ w := by
  induction h generalizing j with
  | refl => exact ⟨Or.inr hq, by simp⟩
  | @tail q₂ q₃ w a h₁ hd ih =>
    subst hq
    rcases hd with ⟨j', h⟩ | ⟨j', b, hb, h⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      obtain ⟨hp, rfl⟩ := blowup_star_none h₁ rfl
      exact ⟨Or.inl hp, by simp⟩
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hp, hw⟩ := ih _ rfl
      refine ⟨hp, ?_⟩
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨hw, fun h => hb h.symm⟩

theorem blowup_star_self {k : ℕ} (j : Fin k) (w : List (Fin k)) (hw : j ∉ w) :
    (blowup k).Star (some j) w (some j) := by
  induction w with
  | nil => exact Star.refl _
  | cons b w ih =>
    simp only [List.mem_cons, not_or] at hw
    have := Star.head (A := blowup k) (a := some b)
      (Or.inr ⟨j, b, fun h => hw.1 h.symm, rfl⟩) (ih hw.2)
    simpa using this

theorem blowup_mem_reach {k : ℕ} (j : Fin k) (w : List (Fin k)) :
    some j ∈ (blowup k).reach w ↔ j ∉ w := by
  constructor
  · rintro ⟨s, -, hs⟩
    exact (blowup_star_some hs j rfl).2
  · intro hw
    refine ⟨none, rfl, ?_⟩
    simpa using (Star.single (A := blowup k) (a := none)
      (Or.inl ⟨j, rfl⟩)).trans (blowup_star_self j w hw)

/-- The loop of Algorithm `quasi_det_sfsa` runs at least `2^k` times on `blowup k`. -/
theorem blowup_iterations (k : ℕ) [NeZero k] : 2 ^ k ≤ quasiDetIterations (blowup k) id := by
  classical
  let f : Finset (Fin k) → ∀ i, QuasiState (id : Option (Fin k) → Option (Fin k)) i :=
    fun J => ((blowup k).quasiDet id).deltaStar ((blowup k).quasiDet id).start J.toList
  have hval : ∀ J (j : Fin k), some j ∈ (f J j).1 ↔ j ∉ J := fun J j => by
    simp only [f]
    rw [deltaStar_quasiDet (blowup_isSeparator k), Set.mem_inter_iff, blowup_mem_reach,
      Finset.mem_toList]
    exact ⟨fun h => h.1, fun h => ⟨h, Or.inr rfl⟩⟩
  have hf : Function.Injective f := fun J J' h => by
    ext j
    have := hval J j
    rw [h, hval J' j] at this
    exact not_iff_not.mp this.symm
  have hsub : Set.range f ⊆
      reachable ((blowup k).quasiDet id).delta ((blowup k).quasiDet id).start := by
    rintro _ ⟨J, rfl⟩; exact ⟨J.toList, rfl⟩
  calc 2 ^ k = (Set.univ : Set (Finset (Fin k))).ncard := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
    _ = (f '' Set.univ).ncard := (Set.ncard_image_of_injective _ hf).symm
    _ ≤ _ := Set.ncard_le_ncard (by rw [Set.image_univ]; exact hsub) (Set.toFinite _)

theorem blowup_sepX (k : ℕ) : (sepX (id : Option (Fin k) → Option (Fin k))).ncard = 1 := by
  have : sepX (id : Option (Fin k) → Option (Fin k)) = {none} := by ext q; simp [sepX]
  rw [this, Set.ncard_singleton]

theorem blowup_block (k : ℕ) (i : Fin k) :
    {q : Option (Fin k) | id q = some i}.ncard = 1 := by
  have : {q : Option (Fin k) | id q = some i} = {some i} := by ext q; simp
  rw [this, Set.ncard_singleton]

/-- The thesis' bound on the number of loop iterations, `2^{|X|}(1 + Σᵢ 2^{|Q_i|})`. -/
noncomputable def thesisIterationBound (part : Q → Option (Fin k)) : ℕ :=
  2 ^ (sepX part).ncard * (1 + ∑ i, 2 ^ {q | part q = some i}.ncard)

/-- The thesis' runtime bound `k|Σ||Q|2^{|X|}Σᵢ2^{|Q_i|}`. -/
noncomputable def thesisRuntimeBound (_A : FSA α Q) (part : Q → Option (Fin k)) : ℕ :=
  k * Nat.card α * Nat.card Q * 2 ^ (sepX part).ncard * ∑ i, 2 ^ {q | part q = some i}.ncard

theorem blowup_thesisIterationBound (k : ℕ) [NeZero k] :
    thesisIterationBound (id : Option (Fin k) → Option (Fin k)) = 4 * k + 2 := by
  simp only [thesisIterationBound, blowup_sepX, blowup_block, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

theorem blowup_thesisRuntimeBound (k : ℕ) [NeZero k] :
    thesisRuntimeBound (blowup k) id = 4 * k ^ 3 * (k + 1) := by
  simp only [thesisRuntimeBound, blowup_sepX, blowup_block, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_option]
  ring

/-- The thesis' bound on the number of loop iterations is false: it fails for `blowup k` for
every `k ≥ 5` (`4k + 2 < 2^k`). -/
theorem thesis_iteration_bound_false (k : ℕ) [NeZero k] (hk : 5 ≤ k) :
    (blowup k).IsSeparator id ∧
      thesisIterationBound (id : Option (Fin k) → Option (Fin k)) <
        quasiDetIterations (blowup k) id := by
  refine ⟨blowup_isSeparator k, ?_⟩
  rw [blowup_thesisIterationBound]
  refine lt_of_lt_of_le ?_ (blowup_iterations k)
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : NeZero n := ⟨by omega⟩
    have := ih
    rw [pow_succ]
    omega

theorem exists_mul_pow_four_lt_two_pow (C : ℕ) : ∃ n : ℕ, C * (n + 1) ^ 4 < 2 ^ (n + 1) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 4 (r := (2 : ℝ)) one_lt_two
  have hε : (0 : ℝ) < 1 / (C + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hε))
  refine ⟨N, ?_⟩
  have h1 := hN (N + 1) (by omega)
  have h2 : (0 : ℝ) < 2 ^ (N + 1) := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at h1
  have h3 : ((C : ℝ)) * ((N + 1 : ℕ) : ℝ) ^ 4 < 2 ^ (N + 1) := by
    have : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 4 := by positivity
    nlinarith
  exact_mod_cast h3

/-- The thesis' runtime bound `O(k|Σ||Q|2^{|X|}Σᵢ2^{|Q_i|})` is false: for every constant `C`
some `blowup k` needs more than `C` times that many loop iterations alone. -/
theorem thesis_runtime_bound_false (C : ℕ) :
    ∃ n : ℕ, (blowup (n + 1)).IsSeparator id ∧
      C * thesisRuntimeBound (blowup (n + 1)) id < quasiDetIterations (blowup (n + 1)) id := by
  obtain ⟨n, hn⟩ := exists_mul_pow_four_lt_two_pow (8 * C)
  refine ⟨n, blowup_isSeparator _, ?_⟩
  rw [blowup_thesisRuntimeBound]
  refine lt_of_lt_of_le ?_ (blowup_iterations (n + 1))
  have : 4 * (n + 1) ^ 3 * (n + 1 + 1) ≤ 8 * (n + 1) ^ 4 := by
    have : n + 1 + 1 ≤ 2 * (n + 1) := by omega
    calc 4 * (n + 1) ^ 3 * (n + 1 + 1) ≤ 4 * (n + 1) ^ 3 * (2 * (n + 1)) :=
          Nat.mul_le_mul_left _ this
      _ = 8 * (n + 1) ^ 4 := by ring
  calc C * (4 * (n + 1) ^ 3 * (n + 1 + 1)) ≤ C * (8 * (n + 1) ^ 4) := Nat.mul_le_mul_left _ this
    _ = 8 * C * (n + 1) ^ 4 := by ring
    _ < 2 ^ (n + 1) := hn

end FSA

end Sqdfsa
