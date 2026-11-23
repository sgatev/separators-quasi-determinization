import Sqdfsa.Separated
import Sqdfsa.QDFA
import Sqdfsa.Reach

/-!
# Quasi-determinization of separated finite-state automata (thesis §3.5)

Given a `k`-separated FSA `A` (partition `part : Q → Option (Fin k)`), we build the QDFA
`A'` with
* `Q'_i = {P ⊆ 𝒞(Q_i)}`, separator type `{E ⊆ X}` (the thesis' `2^X`),
* `s^i = Δ̂ᵢ_ε(S)`, `F'_i = {P | P ∩ F ≠ ∅}`,
* `τ_i(P, σ) = Δ̂ᵢ_ε(Δ̂_f(P, {σ}))`, `ρ_i(P) = P ∩ X`,
* `η_i(P, E) = P ∪ Δ̂ᵢ_ε(E)`, `η_x(E, E') = E ∪ E'`.

The thesis builds these tables incrementally, only on states reachable from `s`
(`𝒜'^{(n)}`, `R^{(n)}`). Here the tables are total; the incremental construction is their
restriction to reachable states, and `reach_stabilizes` is Lemma `quasidet_completion`.

The key invariant (`deltaStar_quasiDet`) is sharper than what the thesis proves:
`δ*(s, w)^i = {q | ∃ s ∈ S, ⟨s, w, q⟩ ∈ Δ*} ∩ 𝒞(Q_i)`, i.e. the QDFA computes exactly the
projections of the subset-construction state onto the components. Both inclusion lemmas
(`quasidet_inclusion_right/left`) follow from it.
-/

namespace Sqdfsa

namespace FSA

variable {α Q : Type*} {k : ℕ} [NeZero k] (A : FSA α Q) (part : Q → Option (Fin k))

/-- The quasi-states of component `i`: subsets of `𝒞(Q_i)`. -/
abbrev QuasiState (i : Fin k) := {P : Set Q // P ⊆ comp part i}

/-- Separator states: subsets of `X`. -/
abbrev SepState := {E : Set Q // E ⊆ sepX part}

/-- The quasi-determinization `𝒜'` of `A`. -/
def quasiDet : QDFA α k (QuasiState part) (SepState part) where
  start i := ⟨A.compClose part i A.start, compClose_subset i _⟩
  final _ := {P | (P.1 ∩ A.final).Nonempty}
  tau i P a := ⟨A.compClose part i (A.stepSet P.1 a), compClose_subset i _⟩
  rho _ P := ⟨P.1 ∩ sepX part, Set.inter_subset_right⟩
  eta i P E := ⟨P.1 ∪ A.compClose part i E.1, Set.union_subset P.2 (compClose_subset i _)⟩
  etaX E E' := ⟨E.1 ∪ E'.1, Set.union_subset E.2 E'.2⟩

/-- States reachable from `S` by reading `w`. -/
def reach (w : List α) : Set Q := {q | ∃ s ∈ A.start, A.Star s w q}

variable {A part}

theorem mem_deltaX_quasiDet (q : ∀ i, QuasiState part i) (a : α) (x : Q) :
    x ∈ ((A.quasiDet part).deltaX q a).1 ↔
      ∃ r, x ∈ A.compClose part r (A.stepSet (q r).1 a) ∧ x ∈ sepX part :=
  mem_iterEtaX _ Subtype.val (fun _ _ => rfl) _ x

theorem delta_quasiDet_val (q : ∀ i, QuasiState part i) (a : α) (i : Fin k) :
    ((A.quasiDet part).delta q a i).1 =
      A.compClose part i (A.stepSet (q i).1 a) ∪
        A.compClose part i ((A.quasiDet part).deltaX q a).1 := rfl

/-- One step of the invariant: if the current quasi-states are the projections of `reach w`,
the next ones are the projections of `reach (w ++ [a])`. -/
theorem delta_quasiDet_reach (hA : A.IsSeparator part) (w : List α) (a : α)
    (q : ∀ i, QuasiState part i) (hq : ∀ i, (q i).1 = A.reach w ∩ comp part i) (i : Fin k) :
    ((A.quasiDet part).delta q a i).1 = A.reach (w ++ [a]) ∩ comp part i := by
  rw [delta_quasiDet_val]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff]
  constructor
  · -- soundness (`quasidet_inclusion_left`)
    rintro (⟨hx, p, ⟨y, hy, hyp⟩, hpx⟩ | ⟨hx, e, he, hex⟩)
    · rw [hq] at hy
      obtain ⟨s, hs, hsy⟩ := hy.1
      exact ⟨⟨s, hs, Star.snoc_iff.mpr ⟨y, p, hsy, hyp, hpx⟩⟩, hx⟩
    · obtain ⟨r, ⟨-, p, ⟨y, hy, hyp⟩, hpe⟩, -⟩ := (mem_deltaX_quasiDet q a e).mp he
      rw [hq] at hy
      obtain ⟨s, hs, hsy⟩ := hy.1
      have : A.Star s (w ++ [a]) e := Star.snoc_iff.mpr ⟨y, p, hsy, hyp, hpe⟩
      exact ⟨⟨s, hs, by simpa using this.trans hex⟩, hx⟩
  · -- completeness (`quasidet_inclusion_right`)
    rintro ⟨⟨s, hs, hsx⟩, hx⟩
    obtain ⟨y, z, hsy, hyz, hzx⟩ := Star.snoc_iff.mp hsx
    have hyR : y ∈ A.reach w := ⟨s, hs, hsy⟩
    by_cases hyi : y ∈ comp part i
    · -- the `a`-transition leaves a state of `𝒞(Q_i)`: handled by `τ_i`
      refine Or.inl ⟨hx, z, ⟨y, ?_, hyz⟩, hzx⟩
      rw [hq]; exact ⟨hyR, hyi⟩
    · -- otherwise `y ∈ Q_r` for some `r ≠ i`, and the `ε`-run from `z` crosses `X`
      obtain ⟨r, hr⟩ : ∃ r, part y = some r := by
        rcases h : part y with _ | r
        · exact absurd (Or.inl h) hyi
        · exact ⟨r, rfl⟩
      have hri : r ≠ i := by rintro rfl; exact hyi (Or.inr hr)
      have hz : z ∈ comp part r := mem_comp_of_delta hA hyz hr
      obtain ⟨e, he, w₁, w₂, hw, hze, hex⟩ := exists_sep_of_star hA hzx hz hx hri
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw.symm
      refine Or.inr ⟨hx, e, (mem_deltaX_quasiDet q a e).mpr ⟨r, ⟨Or.inl he, z, ⟨y, ?_, hyz⟩,
        hze⟩, he⟩, hex⟩
      rw [hq]; exact ⟨hyR, Or.inr hr⟩

/-- The central invariant: `δ*(s, w)^i = reach(w) ∩ 𝒞(Q_i)`. -/
theorem deltaStar_quasiDet (hA : A.IsSeparator part) (w : List α) (i : Fin k) :
    ((A.quasiDet part).deltaStar (A.quasiDet part).start w i).1 = A.reach w ∩ comp part i := by
  induction w using List.reverseRecOn generalizing i with
  | nil =>
    ext x
    simp only [QDFA.deltaStar_nil, quasiDet, compClose, reach, Set.mem_ofPred_eq,
      Set.mem_inter_iff]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩
  | append_singleton w a ih =>
    rw [QDFA.deltaStar_append_singleton]
    exact delta_quasiDet_reach hA w a _ ih i

/-- Theorem (§3.5): the quasi-determinization recognizes the language of `A`
(Lemmas `quasidet_inclusion_right` and `quasidet_inclusion_left`). -/
theorem quasiDet_language (hA : A.IsSeparator part) : (A.quasiDet part).language = A.language := by
  ext w
  show (∃ i, (((A.quasiDet part).deltaStar (A.quasiDet part).start w i).1 ∩ A.final).Nonempty) ↔
    w ∈ A.language
  simp only [deltaStar_quasiDet hA]
  constructor
  · rintro ⟨i, f, ⟨⟨s, hs, hsf⟩, -⟩, hf⟩
    exact ⟨s, hs, f, hf, hsf⟩
  · rintro ⟨s, hs, f, hf, hsf⟩
    obtain ⟨i, hi⟩ : ∃ i, f ∈ comp part i := by
      rcases h : part f with _ | i
      · exact ⟨0, Or.inl h⟩
      · exact ⟨i, Or.inr h⟩
    exact ⟨i, f, ⟨⟨s, hs, hsf⟩, hi⟩, hf⟩

/-- Theorem (§3.5): every separated FSA has an equivalent quasi-deterministic FSA whose
`i`-th component has at most `2^{|𝒞(Q_i)|} = 2^{|Q_i| + |X|}` states and whose separator
alphabet has `2^{|X|}` elements. -/
theorem exists_quasiDet [Finite Q] (hA : A.IsSeparator part) :
    ∃ M : QDFA α k (QuasiState part) (SepState part),
      M.language = A.language ∧
      (∀ i, Nat.card (QuasiState part i) = 2 ^ Nat.card (comp part i)) ∧
      Nat.card (SepState part) = 2 ^ Nat.card (sepX part) := by
  have card_powerset : ∀ C : Set Q, Nat.card {P : Set Q // P ⊆ C} = 2 ^ Nat.card C := by
    intro C
    have := Fintype.ofFinite Q
    classical
    rw [show Nat.card {P : Set Q // P ⊆ C} = Nat.card (𝒫 C) from rfl,
      Nat.card_congr (Equiv.Set.powerset C), Nat.card_eq_fintype_card, Fintype.card_set,
      ← Nat.card_eq_fintype_card]
  exact ⟨A.quasiDet part, quasiDet_language hA, fun i => card_powerset _, card_powerset _⟩

/-! ### Lemma `quasidet_completion` -/

/-- Lemma `quasidet_completion`: the sequence `R^{(n)}` of the incremental construction
stabilizes, and its limit is the set of all states reachable from `s`. -/
theorem reach_stabilizes [Finite Q] :
    ∃ m, ∀ n ≥ m,
      reachR (A.quasiDet part).delta (A.quasiDet part).start n =
        reachR (A.quasiDet part).delta (A.quasiDet part).start (n + 1) ∧
      reachR (A.quasiDet part).delta (A.quasiDet part).start n =
        reachable (A.quasiDet part).delta (A.quasiDet part).start :=
  reachR_stabilizes (Set.toFinite _)

end FSA

end Sqdfsa
