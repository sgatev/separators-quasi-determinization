import Sqdfsa.PerComponent

/-!
# Essential states (thesis §3.1 and §3.5)

The essential states `Q^Σ` of an FSA are its start states and the targets of transitions
labelled with a symbol (not `ε`). Every quasi-state that the constructions produce is
`ε`-closed and determined by its essential states in `Q_i` and its separator states, so the
bounds `2^{|Q_i| + |X|}` improve to `2^{m_i + |X|}` with `m_i = |Q_i ∩ Q^Σ|`.

Results:
* `compClose_eq_essential`: Proposition `essential_closure`,
  `Δ̂ᵢ_ε(Z) = Δ̂ᵢ_ε((Z ∩ Q_i) ∪ (Δ̂ᵢ_ε(Z) ∩ X))` for `Z ⊆ Q^Σ ∪ X`.
* `compStates_subset_kernels`, `ncard_compStates_le_essential`: Lemma `quasidet_essential`,
  `|U_i ∪ T_i| ≤ 2^{m_i + |X|}` (and the same for `U_i` and `T_i`).
* `perComponentCost_le_essential`: Theorem `quasidet_components_essential`, the per-component
  construction takes `O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ 2^{m_i})` time.
-/

set_option linter.unusedSectionVars false

namespace Sqdfsa

namespace FSA

variable {α Q : Type*} {k : ℕ} [NeZero k] {A : FSA α Q} {part : Q → Option (Fin k)}

variable (A) in
/-- The essential states `Q^Σ`: start states and targets of symbol transitions. -/
def essential : Set Q := A.start ∪ {q | ∃ p a, (p, some a, q) ∈ A.delta}

theorem start_subset_essential : A.start ⊆ A.essential := Set.subset_union_left

theorem stepSet_subset_essential (P : Set Q) (a : α) : A.stepSet P a ⊆ A.essential :=
  fun _ ⟨p, _, h⟩ => Or.inr ⟨p, a, h⟩

theorem compClose_union (i : Fin k) (P P' : Set Q) :
    A.compClose part i (P ∪ P') = A.compClose part i P ∪ A.compClose part i P' := by
  ext q
  constructor
  · rintro ⟨hq, p, hp | hp, hs⟩
    exacts [Or.inl ⟨hq, p, hp, hs⟩, Or.inr ⟨hq, p, hp, hs⟩]
  · rintro (⟨hq, p, hp, hs⟩ | ⟨hq, p, hp, hs⟩)
    exacts [⟨hq, p, Or.inl hp, hs⟩, ⟨hq, p, Or.inr hp, hs⟩]

/-- Proposition `essential_closure`: for `Z ⊆ Q^Σ ∪ X`,
`Δ̂ᵢ_ε(Z) = Δ̂ᵢ_ε((Z ∩ Q_i) ∪ (Δ̂ᵢ_ε(Z) ∩ X))`. (The hypothesis on `Z` is only needed for the
consequence that `Z ∩ Q_i` consists of essential states.) -/
theorem compClose_eq_essential (hA : A.IsSeparator part) (i : Fin k) (Z : Set Q) :
    A.compClose part i Z =
      A.compClose part i ((Z ∩ {q | part q = some i}) ∪ (A.compClose part i Z ∩ sepX part)) := by
  ext q
  constructor
  · rintro ⟨hq, z, hz, hs⟩
    by_cases hzi : part z = some i
    · exact ⟨hq, z, Or.inl ⟨hz, hzi⟩, hs⟩
    by_cases hqX : q ∈ sepX part
    · exact ⟨hq, q, Or.inr ⟨⟨hq, z, hz, hs⟩, hqX⟩, Star.refl q⟩
    by_cases hzX : z ∈ sepX part
    · exact ⟨hq, z, Or.inr ⟨⟨sepX_subset_comp i hzX, z, hz, Star.refl z⟩, hzX⟩, hs⟩
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hzX
    have hzj : z ∈ comp part j := Or.inr hj
    have hij : j ≠ i := fun h => hzi (h ▸ hj)
    obtain ⟨x, hx, w₁, w₂, hw, h₁, h₂⟩ := exists_sep_of_star hA hs hzj hq hij
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw.symm
    exact ⟨hq, x, Or.inr ⟨⟨sepX_subset_comp i hx, z, hz, h₁⟩, hx⟩, h₂⟩
  · rintro ⟨hq, p, hp | ⟨⟨-, z, hz, hs⟩, -⟩, hs'⟩
    · exact ⟨hq, p, hp.1, hs'⟩
    · exact ⟨hq, z, hz, hs.eps_trans hs'⟩

variable (A part) in
/-- The sets `Δ̂ᵢ_ε(B ∪ E)` for `B ⊆ Q_i ∩ Q^Σ` and `E ⊆ X`. -/
def kernels (i : Fin k) : Set (Set Q) :=
  (fun BE : Set Q × Set Q => A.compClose part i (BE.1 ∪ BE.2)) ''
    (𝒫 (A.essential ∩ {q | part q = some i}) ×ˢ 𝒫 (sepX part))

theorem compClose_mem_kernels (hA : A.IsSeparator part) (i : Fin k) {Z : Set Q}
    (hZ : Z ⊆ A.essential ∪ sepX part) : A.compClose part i Z ∈ A.kernels part i := by
  refine ⟨(Z ∩ {q | part q = some i}, A.compClose part i Z ∩ sepX part),
    ⟨fun q hq => ⟨?_, hq.2⟩, Set.inter_subset_right⟩, (compClose_eq_essential hA i Z).symm⟩
  rcases hZ hq.1 with h | h
  · exact h
  · exact absurd (hq.2.symm.trans h) (by simp)

theorem mem_reachable_cases {S β : Type*} {δ : S → β → S} {s p : S}
    (hp : p ∈ reachable δ s) : p = s ∨ ∃ p' b, p = δ p' b := by
  obtain ⟨w, rfl⟩ := hp
  rcases List.eq_nil_or_concat w with rfl | ⟨L, b, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨L.foldl δ s, b, by simp⟩

/-- Lemma `quasidet_essential`: every quasi-state of `𝒜''` is `Δ̂ᵢ_ε(B ∪ E)` with
`B ⊆ Q_i ∩ Q^Σ` and `E ⊆ X`. -/
theorem compStates_subset_kernels (hA : A.IsSeparator part) (i : Fin k) :
    Subtype.val '' A.compStates part i ⊆ A.kernels part i := by
  have htau : ∀ (P : QuasiState part i) a,
      ((A.quasiDet part).tau i P a).1 ∈ A.kernels part i := fun P a =>
    compClose_mem_kernels hA i ((stepSet_subset_essential _ _).trans Set.subset_union_left)
  rintro _ ⟨P, hP | ⟨P', -, a, rfl⟩, rfl⟩
  · rcases mem_reachable_cases hP with rfl | ⟨P', ⟨a, E⟩, rfl⟩
    · exact compClose_mem_kernels hA i (start_subset_essential.trans Set.subset_union_left)
    · show A.compClose part i (A.stepSet P'.1 a) ∪ A.compClose part i E.1 ∈ _
      rw [← compClose_union]
      exact compClose_mem_kernels hA i
        (Set.union_subset_union (stepSet_subset_essential _ _) E.2)
  · exact htau P' a

theorem ncard_kernels_le [Finite Q] (i : Fin k) :
    (A.kernels part i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (sepX part).ncard) := by
  refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
  rw [Set.ncard_prod, Set.ncard_powerset, Set.ncard_powerset, pow_add]

/-- Lemma `quasidet_essential`: `|U_i ∪ T_i| ≤ 2^{m_i + |X|}`, hence also for `U_i` and
`T_i`. -/
theorem ncard_compStates_le_essential [Finite Q] (hA : A.IsSeparator part) (i : Fin k) :
    (A.compStates part i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (sepX part).ncard) := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  exact (Set.ncard_le_ncard (compStates_subset_kernels hA i) (Set.toFinite _)).trans
    (ncard_kernels_le i)

theorem ncard_compClosure_le_essential [Finite Q] (hA : A.IsSeparator part) (i : Fin k) :
    (A.compClosure part i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (sepX part).ncard) :=
  (Set.ncard_le_ncard Set.subset_union_left (Set.toFinite _)).trans
    (ncard_compStates_le_essential hA i)

theorem ncard_tauImage_le_essential [Finite Q] (hA : A.IsSeparator part) (i : Fin k) :
    (A.tauImage part i).ncard ≤
      2 ^ ((A.essential ∩ {q | part q = some i}).ncard + (sepX part).ncard) :=
  (Set.ncard_le_ncard Set.subset_union_right (Set.toFinite _)).trans
    (ncard_compStates_le_essential hA i)

/-- Theorem `quasidet_components_essential`: the per-component construction takes
`O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ 2^{m_i})` time. -/
theorem perComponentCost_le_essential [Finite Q] (hA : A.IsSeparator part) :
    perComponentCost (Nat.card α) (sepX part).ncard (Nat.card Q)
        (fun i => (A.compClosure part i).ncard) (fun i => (A.tauImage part i).ncard) ≤
      3 * (Nat.card α + 2 ^ (sepX part).ncard + 1) * Nat.card Q * 2 ^ (sepX part).ncard *
        ∑ i, 2 ^ (A.essential ∩ {q | part q = some i}).ncard :=
  perComponentCost_le_of _ _ _ _ _ _ (fun i => ncard_compClosure_le_essential hA i)
    (fun i => ncard_tauImage_le_essential hA i)

end FSA

end Sqdfsa
