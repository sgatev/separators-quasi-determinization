import Sqdfsa.Essential

/-!
# Quasi-determinization with boundaries (thesis §3.5)

The quasi-states of `𝒜'` and `𝒜''` are subsets of `𝒞(Q_i) = Q_i ∪ X`, and `η_i` is tabulated
for all `2^{|X|}` separator states. Component `i`, however, only interacts with the separator
states adjacent to `Q_i`. Boundaries `X_1, …, X_k ⊆ X` (`IsBoundary`) are sets such that

* every transition with an endpoint in `Q_i` has both endpoints in the bag `B_i = Q_i ∪ X_i`,
* `X_1 ∪ … ∪ X_k = X`.

The construction `𝒜ᵇ` (`boundaryDet`) keeps `τ_i`, `ρ_i` and `η_x` of `𝒜'`, starts from
`Δ̂_ε(S) ∩ B_i`, and replaces `η_i` with `ηᵇ_i(t, x) = (t ∩ B_i) ∪ (Δ̂_ε(x ∩ X_i) ∩ B_i)`, which
reads only `x ∩ X_i`.

Results:
* `deltaStar_boundaryDet`: Lemma `boundary_invariant`, `δ*(s, w)^i = Reach(w) ∩ B_i`, and
  `boundaryDet_language`: `𝒜ᵇ` recognizes `𝓛_A`.
* `eclose_inter_bag_eq`: Proposition `boundary_essential_closure`.
* `ncard_bndClosure_le`, `ncard_bndTauImage_le`: Lemma `boundary_essential`, the explored
  quasi-states `Uᵇ_i` and the rows `Tᵇ_i` of `ηᵇ_i` number at most `2^{m_i + |X_i|}` each.
* `boundaryCost_le`: Theorem `quasidet_boundaries`, the per-component construction with
  boundaries takes `O(Σᵢ (|Σ| + 2^{|X_i|})·|Q|·2^{m_i + |X_i|})` time.
-/

set_option linter.unusedSectionVars false

namespace Sqdfsa

namespace FSA

variable {α Q : Type*} {k : ℕ} [NeZero k] {A : FSA α Q} {part : Q → Option (Fin k)}
  {bnd : Fin k → Set Q}

variable (part bnd) in
/-- The bag `B_i = Q_i ∪ X_i`. -/
def bag (i : Fin k) : Set Q := {q | part q = some i} ∪ (bnd i ∩ sepX part)

theorem bag_subset_comp (i : Fin k) : bag part bnd i ⊆ comp part i := by
  rintro q (h | ⟨-, h⟩)
  exacts [Or.inr h, Or.inl h]

variable (A part bnd) in
/-- `X_1, …, X_k` are boundaries of the separation `part`. -/
structure IsBoundary : Prop where
  /-- Every transition with an endpoint in `Q_i` stays within `B_i`. -/
  adj : ∀ {p q : Q} {a : Option α} (i : Fin k), (p, a, q) ∈ A.delta →
    (part p = some i ∨ part q = some i) → p ∈ bag part bnd i ∧ q ∈ bag part bnd i
  /-- The boundaries cover the separator. -/
  cover : ∀ x ∈ sepX part, ∃ i, x ∈ bnd i

/-- Boundaries induce a separator: no transition joins two different blocks. -/
theorem IsBoundary.isSeparator (hB : A.IsBoundary part bnd) : A.IsSeparator part := by
  intro p a q i j hd hi hj
  rcases (hB.adj i hd (Or.inl hi)).2 with h | ⟨-, h⟩
  · exact Option.some_injective _ (h.symm.trans hj)
  · rw [sepX, Set.mem_ofPred_eq, hj] at h; cases h

/-- A run from outside of `Q_i` into `Q_i` passes through `X_i`. -/
theorem IsBoundary.exists_bnd_of_star (hB : A.IsBoundary part bnd) {i : Fin k} {z q : Q}
    {w : List α} (h : A.Star z w q) (hz : part z ≠ some i) (hq : part q = some i) :
    ∃ x ∈ bnd i ∩ sepX part, ∃ w₁ w₂, w = w₁ ++ w₂ ∧ A.Star z w₁ x ∧ A.Star x w₂ q := by
  induction h with
  | refl => exact absurd hq hz
  | @tail q₂ q₃ w b h₁ h₂ ih =>
    by_cases hq₂ : part q₂ = some i
    · obtain ⟨x, hx, w₁, w₂, rfl, hzx, hxq⟩ := ih hq₂
      exact ⟨x, hx, w₁, w₂ ++ b.toList, by simp, hzx, hxq.tail h₂⟩
    · rcases (hB.adj i h₂ (Or.inr hq)).1 with h | h
      · exact absurd h hq₂
      · exact ⟨q₂, h, w, b.toList, rfl, h₁, Star.single h₂⟩

variable (A part bnd) in
/-- The quasi-determinization with boundaries `𝒜ᵇ`. -/
def boundaryDet : QDFA α k (QuasiState part) (SepState part) where
  start i := ⟨A.eclose A.start ∩ bag part bnd i, Set.inter_subset_right.trans (bag_subset_comp i)⟩
  final _ := {P | (P.1 ∩ A.final).Nonempty}
  tau := (A.quasiDet part).tau
  rho := (A.quasiDet part).rho
  eta i P E := ⟨(P.1 ∩ bag part bnd i) ∪ (A.eclose (E.1 ∩ bnd i) ∩ bag part bnd i),
    Set.union_subset (Set.inter_subset_right.trans (bag_subset_comp i))
      (Set.inter_subset_right.trans (bag_subset_comp i))⟩
  etaX := (A.quasiDet part).etaX

/-- `ηᵇ_i(t, x)` depends only on `t ∩ B_i` and `x ∩ X_i`, so it suffices to tabulate it for the
distinct values of `t ∩ B_i` and the subsets of `X_i`. -/
theorem boundaryDet_eta_congr (i : Fin k) {P P' : QuasiState part i} {E E' : SepState part}
    (hP : P.1 ∩ bag part bnd i = P'.1 ∩ bag part bnd i) (hE : E.1 ∩ bnd i = E'.1 ∩ bnd i) :
    (A.boundaryDet part bnd).eta i P E = (A.boundaryDet part bnd).eta i P' E' := by
  apply Subtype.ext
  simp only [boundaryDet, hP, hE]

theorem mem_deltaX_boundaryDet (q : ∀ i, QuasiState part i) (a : α) (x : Q) :
    x ∈ ((A.boundaryDet part bnd).deltaX q a).1 ↔
      ∃ r, x ∈ A.compClose part r (A.stepSet (q r).1 a) ∧ x ∈ sepX part :=
  mem_iterEtaX _ Subtype.val (fun _ _ => rfl) _ x

/-- The separator state after a step is `Reach(w σ) ∩ X`. -/
theorem deltaX_boundaryDet_reach (hB : A.IsBoundary part bnd) (w : List α) (a : α)
    (q : ∀ i, QuasiState part i) (hq : ∀ i, (q i).1 = A.reach w ∩ bag part bnd i) (x : Q) :
    x ∈ ((A.boundaryDet part bnd).deltaX q a).1 ↔ x ∈ A.reach (w ++ [a]) ∧ x ∈ sepX part := by
  rw [mem_deltaX_boundaryDet]
  constructor
  · rintro ⟨r, ⟨-, p, ⟨y, hy, hyp⟩, hpx⟩, hx⟩
    rw [hq] at hy
    obtain ⟨s, hs, hsy⟩ := hy.1
    exact ⟨⟨s, hs, Star.snoc_iff.mpr ⟨y, p, hsy, hyp, hpx⟩⟩, hx⟩
  · rintro ⟨⟨s, hs, hsx⟩, hx⟩
    obtain ⟨y, z, hsy, hyz, hzx⟩ := Star.snoc_iff.mp hsx
    obtain ⟨r, hr⟩ : ∃ r, y ∈ bag part bnd r := by
      rcases h : part y with _ | r
      · obtain ⟨r, hr⟩ := hB.cover y h
        exact ⟨r, Or.inr ⟨hr, h⟩⟩
      · exact ⟨r, Or.inl h⟩
    refine ⟨r, ⟨sepX_subset_comp r hx, z, ⟨y, ?_, hyz⟩, hzx⟩, hx⟩
    rw [hq]; exact ⟨⟨s, hs, hsy⟩, hr⟩

/-- One step of Lemma `boundary_invariant`. -/
theorem delta_boundaryDet_reach (hB : A.IsBoundary part bnd) (w : List α) (a : α)
    (q : ∀ i, QuasiState part i) (hq : ∀ i, (q i).1 = A.reach w ∩ bag part bnd i) (i : Fin k) :
    ((A.boundaryDet part bnd).delta q a i).1 = A.reach (w ++ [a]) ∩ bag part bnd i := by
  have hX := deltaX_boundaryDet_reach hB w a q hq
  show (A.compClose part i (A.stepSet (q i).1 a) ∩ bag part bnd i) ∪
      (A.eclose (((A.boundaryDet part bnd).deltaX q a).1 ∩ bnd i) ∩ bag part bnd i) = _
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff]
  constructor
  · rintro (⟨⟨-, p, ⟨y, hy, hyp⟩, hpx⟩, hx⟩ | ⟨⟨e, ⟨he, -⟩, hex⟩, hx⟩)
    · rw [hq] at hy
      obtain ⟨s, hs, hsy⟩ := hy.1
      exact ⟨⟨s, hs, Star.snoc_iff.mpr ⟨y, p, hsy, hyp, hpx⟩⟩, hx⟩
    · obtain ⟨⟨s, hs, hse⟩, -⟩ := (hX e).mp he
      exact ⟨⟨s, hs, by simpa using hse.trans hex⟩, hx⟩
  · rintro ⟨⟨s, hs, hsx⟩, hx⟩
    obtain ⟨y, z, hsy, hyz, hzx⟩ := Star.snoc_iff.mp hsx
    by_cases hyi : y ∈ bag part bnd i
    · refine Or.inl ⟨⟨bag_subset_comp i hx, z, ⟨y, ?_, hyz⟩, hzx⟩, hx⟩
      rw [hq]; exact ⟨⟨s, hs, hsy⟩, hyi⟩
    · have hxR : x ∈ A.reach (w ++ [a]) := ⟨s, hs, hsx⟩
      rcases hx with hxi | hxb
      · -- `x ∈ Q_i`: the `ε`-run from `z` enters `Q_i` through `X_i`
        have hz : part z ≠ some i := fun hz =>
          hyi (hB.adj i hyz (Or.inr hz)).1
        obtain ⟨e, he, w₁, w₂, hw, hze, hex⟩ := hB.exists_bnd_of_star hzx hz hxi
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw.symm
        have heR : e ∈ A.reach (w ++ [a]) :=
          ⟨s, hs, Star.snoc_iff.mpr ⟨y, z, hsy, hyz, hze⟩⟩
        exact Or.inr ⟨⟨e, ⟨(hX e).mpr ⟨heR, he.2⟩, he.1⟩, hex⟩, Or.inl hxi⟩
      · -- `x ∈ X_i`: it is part of the separator state
        exact Or.inr ⟨⟨x, ⟨(hX x).mpr ⟨hxR, hxb.2⟩, hxb.1⟩, Star.refl x⟩, Or.inr hxb⟩

/-- Lemma `boundary_invariant`: `δ*(s, w)^i = Reach(w) ∩ B_i`. -/
theorem deltaStar_boundaryDet (hB : A.IsBoundary part bnd) (w : List α) (i : Fin k) :
    ((A.boundaryDet part bnd).deltaStar (A.boundaryDet part bnd).start w i).1 =
      A.reach w ∩ bag part bnd i := by
  induction w using List.reverseRecOn generalizing i with
  | nil => rfl
  | append_singleton w a ih =>
    rw [QDFA.deltaStar_append_singleton]
    exact delta_boundaryDet_reach hB w a _ ih i

/-- `𝒜ᵇ` recognizes the language of `A`. -/
theorem boundaryDet_language (hB : A.IsBoundary part bnd) :
    (A.boundaryDet part bnd).language = A.language := by
  ext w
  show (∃ i, (((A.boundaryDet part bnd).deltaStar (A.boundaryDet part bnd).start w i).1 ∩
    A.final).Nonempty) ↔ w ∈ A.language
  simp only [deltaStar_boundaryDet hB]
  constructor
  · rintro ⟨i, f, ⟨⟨s, hs, hsf⟩, -⟩, hf⟩
    exact ⟨s, hs, f, hf, hsf⟩
  · rintro ⟨s, hs, f, hf, hsf⟩
    obtain ⟨i, hi⟩ : ∃ i, f ∈ bag part bnd i := by
      rcases h : part f with _ | i
      · obtain ⟨i, hi⟩ := hB.cover f h
        exact ⟨i, Or.inr ⟨hi, h⟩⟩
      · exact ⟨i, Or.inl h⟩
    exact ⟨i, f, ⟨⟨s, hs, hsf⟩, hi⟩, hf⟩

/-! ### Essential states and the per-component construction -/

/-- Proposition `boundary_essential_closure`:
`Δ̂_ε(Z) ∩ B_i = Δ̂_ε((Z ∩ Q_i) ∪ (Δ̂_ε(Z) ∩ X_i)) ∩ B_i`. -/
theorem eclose_inter_bag_eq (hB : A.IsBoundary part bnd) (i : Fin k) (Z : Set Q) :
    A.eclose Z ∩ bag part bnd i =
      A.eclose ((Z ∩ {q | part q = some i}) ∪ (A.eclose Z ∩ (bnd i ∩ sepX part))) ∩
        bag part bnd i := by
  ext q
  constructor
  · rintro ⟨⟨z, hz, hs⟩, hq⟩
    by_cases hzi : part z = some i
    · exact ⟨⟨z, Or.inl ⟨hz, hzi⟩, hs⟩, hq⟩
    rcases hq with hqi | hqb
    · obtain ⟨x, hx, w₁, w₂, hw, h₁, h₂⟩ := hB.exists_bnd_of_star hs hzi hqi
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw.symm
      exact ⟨⟨x, Or.inr ⟨⟨z, hz, h₁⟩, hx⟩, h₂⟩, Or.inl hqi⟩
    · exact ⟨⟨q, Or.inr ⟨⟨z, hz, hs⟩, hqb⟩, Star.refl q⟩, Or.inr hqb⟩
  · rintro ⟨⟨p, hp | ⟨⟨z, hz, hs⟩, -⟩, hs'⟩, hq⟩
    · exact ⟨⟨p, hp.1, hs'⟩, hq⟩
    · exact ⟨⟨z, hz, hs.eps_trans hs'⟩, hq⟩

theorem eclose_union (P P' : Set Q) : A.eclose (P ∪ P') = A.eclose P ∪ A.eclose P' := by
  ext q
  constructor
  · rintro ⟨p, hp | hp, hs⟩
    exacts [Or.inl ⟨p, hp, hs⟩, Or.inr ⟨p, hp, hs⟩]
  · rintro (⟨p, hp, hs⟩ | ⟨p, hp, hs⟩)
    exacts [⟨p, Or.inl hp, hs⟩, ⟨p, Or.inr hp, hs⟩]

theorem compClose_inter_bag (i : Fin k) (Z : Set Q) :
    A.compClose part i Z ∩ bag part bnd i = A.eclose Z ∩ bag part bnd i := by
  ext q
  constructor
  · rintro ⟨⟨-, h⟩, hb⟩
    exact ⟨h, hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨⟨bag_subset_comp i hb, h⟩, hb⟩

variable (A part bnd) in
/-- The sets `Δ̂_ε(B ∪ E) ∩ B_i` for `B ⊆ Q_i ∩ Q^Σ` and `E ⊆ X_i`. -/
def bndKernels (i : Fin k) : Set (Set Q) :=
  (fun BE : Set Q × Set Q => A.eclose (BE.1 ∪ BE.2) ∩ bag part bnd i) ''
    (𝒫 (A.essential ∩ {q | part q = some i}) ×ˢ 𝒫 (bnd i ∩ sepX part))

theorem eclose_inter_bag_mem (hB : A.IsBoundary part bnd) (i : Fin k) {Z : Set Q}
    (hZ : Z ⊆ A.essential ∪ sepX part) :
    A.eclose Z ∩ bag part bnd i ∈ A.bndKernels part bnd i := by
  refine ⟨(Z ∩ {q | part q = some i}, A.eclose Z ∩ (bnd i ∩ sepX part)),
    ⟨fun q hq => ⟨?_, hq.2⟩, Set.inter_subset_right⟩, (eclose_inter_bag_eq hB i Z).symm⟩
  rcases hZ hq.1 with h | h
  · exact h
  · exact absurd (hq.2.symm.trans h) (by simp)

theorem ncard_bndKernels_le [Finite Q] (i : Fin k) :
    (A.bndKernels part bnd i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (bnd i ∩ sepX part).ncard) := by
  refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
  rw [Set.ncard_prod, Set.ncard_powerset, Set.ncard_powerset, pow_add]

variable (A part bnd) in
/-- One step of the exploration of component `i`: `P ↦ ηᵇ_i(τ_i(P, σ), x)`. -/
def bndStep (i : Fin k) (P : QuasiState part i) (b : α × SepState part) : QuasiState part i :=
  (A.boundaryDet part bnd).eta i ((A.boundaryDet part bnd).tau i P b.1) b.2

variable (A part bnd) in
/-- `Uᵇ_i`: the quasi-states explored by the per-component construction with boundaries. Since
`ηᵇ_i` reads only `x ∩ X_i`, it suffices to apply it for `x ⊆ X_i`. -/
def bndClosure (i : Fin k) : Set (QuasiState part i) :=
  reachable (A.bndStep part bnd i) ((A.boundaryDet part bnd).start i)

variable (A part bnd) in
/-- `Tᵇ_i`: the distinct values `τ_i(P, σ) ∩ B_i` for `P ∈ Uᵇ_i`, the rows of the table of
`ηᵇ_i`. -/
def bndTauImage (i : Fin k) : Set (Set Q) :=
  {t | ∃ P ∈ A.bndClosure part bnd i, ∃ a, t = ((A.boundaryDet part bnd).tau i P a).1 ∩
    bag part bnd i}

/-- Every reachable global state has its `i`-th component in `Uᵇ_i`. -/
theorem deltaStar_mem_bndClosure (w : List α) (i : Fin k) :
    (A.boundaryDet part bnd).deltaStar (A.boundaryDet part bnd).start w i ∈
      A.bndClosure part bnd i := by
  induction w using List.reverseRecOn with
  | nil => exact start_mem_reachable
  | append_singleton w a ih =>
    rw [QDFA.deltaStar_append_singleton]
    exact mem_reachable_step ih (a, (A.boundaryDet part bnd).deltaX _ a)

/-- Lemma `boundary_essential`: the explored quasi-states are of the form `Δ̂_ε(B ∪ E) ∩ B_i`. -/
theorem bndClosure_subset_kernels (hB : A.IsBoundary part bnd) (i : Fin k) :
    Subtype.val '' A.bndClosure part bnd i ⊆ A.bndKernels part bnd i := by
  rintro _ ⟨P, hP, rfl⟩
  rcases mem_reachable_cases hP with rfl | ⟨P', ⟨a, E⟩, rfl⟩
  · exact eclose_inter_bag_mem hB i (start_subset_essential.trans Set.subset_union_left)
  · show A.compClose part i (A.stepSet P'.1 a) ∩ bag part bnd i ∪
        A.eclose (E.1 ∩ bnd i) ∩ bag part bnd i ∈ _
    rw [compClose_inter_bag, ← Set.union_inter_distrib_right, ← eclose_union]
    exact eclose_inter_bag_mem hB i (Set.union_subset_union (stepSet_subset_essential _ _)
      (Set.inter_subset_left.trans E.2))

theorem bndTauImage_subset_kernels (hB : A.IsBoundary part bnd) (i : Fin k) :
    A.bndTauImage part bnd i ⊆ A.bndKernels part bnd i := by
  rintro _ ⟨P, -, a, rfl⟩
  show A.compClose part i (A.stepSet P.1 a) ∩ bag part bnd i ∈ _
  rw [compClose_inter_bag]
  exact eclose_inter_bag_mem hB i ((stepSet_subset_essential _ _).trans Set.subset_union_left)

/-- Lemma `boundary_essential`: `|Uᵇ_i| ≤ 2^{m_i + |X_i|}`. -/
theorem ncard_bndClosure_le [Finite Q] (hB : A.IsBoundary part bnd) (i : Fin k) :
    (A.bndClosure part bnd i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (bnd i ∩ sepX part).ncard) := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  exact (Set.ncard_le_ncard (bndClosure_subset_kernels hB i) (Set.toFinite _)).trans
    (ncard_bndKernels_le i)

/-- Lemma `boundary_essential`: `|Tᵇ_i| ≤ 2^{m_i + |X_i|}`. -/
theorem ncard_bndTauImage_le [Finite Q] (hB : A.IsBoundary part bnd) (i : Fin k) :
    (A.bndTauImage part bnd i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (bnd i ∩ sepX part).ncard) :=
  (Set.ncard_le_ncard (bndTauImage_subset_kernels hB i) (Set.toFinite _)).trans
    (ncard_bndKernels_le i)

/-- The cost of the per-component construction with boundaries, in the cost model of
`perComponentCost`: for each component, initialization (`|Q|`); for each of the `Iᵢ` explored
quasi-states, the final-state test and the worklist bookkeeping (`2|Q|`) and `|Σ|` applications of
`τ_i` and `ρ_i` (`2|Q|` each); for each of the `Jᵢ` rows, `2^{|X_i|}` applications of `ηᵇ_i`, each
with a worklist insertion (`2|Q|` each). There is no table of `η_x`. -/
def boundaryCost (nS nQ : ℕ) (b I J : Fin k → ℕ) : ℕ :=
  ∑ i, (nQ + I i * (2 * nQ + nS * (2 * nQ)) + J i * (2 ^ b i * (2 * nQ)))

omit [NeZero k] in
theorem boundaryCost_le_of (nS nQ : ℕ) (m b I J : Fin k → ℕ)
    (hI : ∀ i, I i ≤ 2 ^ (m i + b i)) (hJ : ∀ i, J i ≤ 2 ^ (m i + b i)) :
    boundaryCost nS nQ b I J ≤ ∑ i, 3 * (nS + 2 ^ b i + 1) * nQ * 2 ^ (m i + b i) := by
  refine Finset.sum_le_sum fun i _ => ?_
  have he : 1 ≤ 2 ^ (m i + b i) := Nat.one_le_two_pow
  have h1 := Nat.mul_le_mul_right (2 * nQ + nS * (2 * nQ)) (hI i)
  have h2 := Nat.mul_le_mul_right (2 ^ b i * (2 * nQ)) (hJ i)
  nlinarith [Nat.zero_le (nS * nQ * 2 ^ (m i + b i)), Nat.zero_le (2 ^ b i * nQ * 2 ^ (m i + b i)),
    Nat.mul_le_mul_left nQ he]

/-- Theorem `quasidet_boundaries`: the per-component construction with boundaries takes
`O(Σᵢ (|Σ| + 2^{|X_i|})·|Q|·2^{m_i + |X_i|})` time. -/
theorem boundaryCost_le [Finite Q] (hB : A.IsBoundary part bnd) :
    boundaryCost (Nat.card α) (Nat.card Q) (fun i => (bnd i ∩ sepX part).ncard)
        (fun i => (A.bndClosure part bnd i).ncard) (fun i => (A.bndTauImage part bnd i).ncard) ≤
      ∑ i, 3 * (Nat.card α + 2 ^ (bnd i ∩ sepX part).ncard + 1) * Nat.card Q *
        2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (bnd i ∩ sepX part).ncard) :=
  boundaryCost_le_of _ _ (fun i => (A.essential ∩ {q | part q = some i}).ncard) _ _ _
    (fun i => ncard_bndClosure_le hB i) (fun i => ncard_bndTauImage_le hB i)

/-- With `X_i = X` for every `i`, a separator gives boundaries. -/
theorem isBoundary_sepX (hA : A.IsSeparator part) : A.IsBoundary part (fun _ => sepX part) := by
  have mem : ∀ {q : Q} (i : Fin k), q ∈ comp part i → q ∈ bag part (fun _ => sepX part) i := by
    rintro q i (h | h)
    exacts [Or.inr ⟨h, h⟩, Or.inl h]
  refine ⟨fun {p q a} i hd h => ?_, fun x hx => ⟨0, hx⟩⟩
  rcases h with h | h
  · exact ⟨Or.inl h, mem i (mem_comp_of_delta hA hd h)⟩
  · refine ⟨mem i ?_, Or.inl h⟩
    rcases hp : part p with _ | j
    · exact Or.inl hp
    · exact Or.inr (by rw [hp, hA p a q j i hd hp h])

end FSA

end Sqdfsa
