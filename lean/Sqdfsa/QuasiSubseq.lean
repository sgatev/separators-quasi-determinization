import Sqdfsa.FST
import Sqdfsa.QSFST
import Sqdfsa.Reach

/-!
# Quasi-subsequentialization of separated finite-state transducers (thesis §4.4)

## The construction, and why it differs from the thesis

The thesis defines
`τ_i(qⁱ, σ) = {⟨p, λ(q, σ)⁻¹w⟩ | ⟨p, w⟩ ∈ Δⁱ_{fε}(qⁱ, σ)}` with `λ(q, σ) = ⋀ⱼ λⱼ(qʲ, σ)`.
The value depends on the *whole* state `q` through the global lcp `λ(q, σ)`, while `τ_i` is
indexed by `qⁱ` alone, so `τ_i^{(n)}` need not be a function. (See the README for a concrete
trimmed functional separated transducer on which two reachable states share `q¹` but get
different `τ_1`-values.)

We keep the thesis' QSFST *definition* unchanged and repair the construction by deferring
normalization to `η_i`, passing the global lcp through the separator channel:
* `τ_i(P, σ) = Δⁱ_{fε}(P, σ)` (un-normalized), `λ_i(P, σ) = ⋀{w | ⟨p, w⟩ ∈ τ_i(P, σ)}`;
* separator states are pairs `⟨ℓ, E⟩`: an lcp and a set of separator pairs;
  `ρ_i(T) = ⟨⋀ outputs(T), T ∩ (X × Ω*)⟩`, `η_x(⟨ℓ, E⟩, ⟨ℓ', E'⟩) = ⟨ℓ ∧ ℓ', E ∪ E'⟩`;
* `η_i(T, ⟨m, E⟩) = {⟨p, m⁻¹w⟩ | ⟨p, w⟩ ∈ T ∪ Δ̂ⁱ_ε(E)}`.
Then `δ_x(q, σ).1 = λ(q, σ)` and every table is a genuine function of its arguments.

## Results

* `deltaStar_quasiSubseq` (the invariant behind Lemmas `quasisubseq_inclusion_right/left`): if
  `λ*(s, w) = o`, then `δ*(s, w)ⁱ` is exactly the set of `⟨p, d⟩` with `p ∈ 𝒞(Q_i)` and
  `⟨s, w, o·d, p⟩ ∈ Δ*` for some `s ∈ S`. Moreover `o` is a prefix of every output on `w`, and
  for `w ≠ ε` it is the longest such prefix. If `λ*(s, w)` is undefined, there are no runs on `w`.
* `quasiSubseq_relation`: for a functional separated `T`, `𝓡_{T'} = 𝓕_T`.
* `quasisubseq_completion`: if `T` is trimmed and `𝓡_T` has bounded variation, only finitely
  many states are reachable, so `R^{(n)}` stabilizes.
-/

set_option linter.unusedSectionVars false

namespace Sqdfsa

/-- When `η_x` is `olcp`, its iteration computes the lcp of the union. -/
theorem iterEtaX_olcp {β : Type*} [DecidableEq β] {k : ℕ} [NeZero k] (W : Fin k → Set (List β))
    (m : Fin k → Option (List β)) (hm : ∀ i, OIsLcp (W i) (m i)) :
    OIsLcp (⋃ i, W i) (iterEtaX olcp m) := by
  have fold : ∀ (l : List (Fin k)) (a : Option (List β)) (A : Set (List β)), OIsLcp A a →
      OIsLcp (A ∪ ⋃ i ∈ l, W i) ((l.map m).foldl olcp a) := by
    intro l
    induction l with
    | nil => intro a A h; simpa using h
    | cons j l ih =>
      intro a A h
      simp only [List.map_cons, List.foldl_cons]
      refine (ih _ _ (h.union (hm j))).congr ?_
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons, exists_prop]
      constructor
      · rintro ((h | h) | ⟨i, hi, h⟩)
        exacts [Or.inl h, Or.inr ⟨j, Or.inl rfl, h⟩, Or.inr ⟨i, Or.inr hi, h⟩]
      · rintro (h | ⟨i, rfl | hi, h⟩)
        exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr ⟨i, hi, h⟩]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  have h := fold ((List.finRange n).map Fin.succ) (m 0) (W 0) (hm 0)
  simp only [iterEtaX, List.finRange_succ, List.map_cons, List.tail_cons, List.map_map] at h ⊢
  refine h.congr ?_
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, List.mem_map, List.mem_finRange, true_and,
    exists_prop]
  constructor
  · rintro (h | ⟨i, -, h⟩)
    exacts [⟨0, h⟩, ⟨i, h⟩]
  · rintro ⟨i, h⟩
    cases i using Fin.cases with
    | zero => exact Or.inl h
    | succ j => exact Or.inr ⟨_, ⟨j, rfl⟩, h⟩

namespace FST

variable {α β Q : Type*} [DecidableEq β] {k : ℕ} [NeZero k] (T : FST α β Q)
  (part : Q → Option (Fin k))

/-- Separator states: an lcp of pending outputs, and a set of separator pairs. -/
abbrev SepData (β Q : Type*) := Option (List β) × Set (Q × List β)

/-- The (repaired) quasi-subsequentialization `𝒯'` of `T`. -/
noncomputable def quasiSubseq : QSFST α β k (fun _ => Set (Q × List β)) (SepData β Q) where
  start i := T.compClose part i (T.start ×ˢ {[]})
  final _ := {P | ∃ x ∈ P, x.1 ∈ T.final}
  tau i P a := T.compStep part i P a
  rho _ P := (setLcp (Prod.snd '' P), {x | x ∈ P ∧ x.1 ∈ sepX part})
  eta i P e := (fun x => (x.1, lquot (e.1.getD []) x.2)) '' (P ∪ T.compClose part i e.2)
  etaX e e' := (olcp e.1 e'.1, e.2 ∪ e'.2)
  lam i P a := setLcp (Prod.snd '' T.compStep part i P a)
  psi _ P := open Classical in if h : ∃ x ∈ P, x.1 ∈ T.final then (Classical.choose h).2 else []

/-- `(state, output)` pairs reached from `S` by reading `w`. -/
def run (w : List α) : Set (Q × List β) := {x | ∃ s ∈ T.start, T.Star s w x.2 x.1}

/-- The `i`-th component projection of a run set, with the common output `o` removed. -/
def proj (o : List β) (R : Set (Q × List β)) (i : Fin k) : Set (Q × List β) :=
  {x | x.1 ∈ comp part i ∧ (x.1, o ++ x.2) ∈ R}

variable {T part}

local notation "𝒯'" => T.quasiSubseq part

theorem mem_deltaX_snd (q : Fin k → Set (Q × List β)) (a : α) (x : Q × List β) :
    x ∈ ((𝒯').deltaX q a).2 ↔ ∃ r, x ∈ T.compStep part r (q r) a ∧ x.1 ∈ sepX part :=
  mem_iterEtaX _ Prod.snd (fun _ _ => rfl) _ x

theorem olam_eq (q : Fin k → Set (Q × List β)) (a : α) :
    (𝒯').olam q a = ((𝒯').deltaX q a).1 :=
  (iterEtaX_hom (𝒯').etaX olcp Prod.fst (fun _ _ => rfl)
    (fun i => (𝒯').rho i ((𝒯').tau i (q i) a))).symm

theorem olam_spec (q : Fin k → Set (Q × List β)) (a : α) :
    OIsLcp (⋃ r, Prod.snd '' T.compStep part r (q r) a) ((𝒯').olam q a) :=
  iterEtaX_olcp _ _ fun _ => setLcp_spec _

theorem delta_eq (q : Fin k → Set (Q × List β)) (a : α) (i : Fin k) :
    (𝒯').delta q a i = (fun x => (x.1, lquot (((𝒯').olam q a).getD []) x.2)) ''
      (T.compStep part i (q i) a ∪ T.compClose part i ((𝒯').deltaX q a).2) := by
  rw [olam_eq]; rfl

theorem psi_spec (i : Fin k) (P : Set (Q × List β)) (h : ∃ x ∈ P, x.1 ∈ T.final) :
    ∃ y ∈ P, y.1 ∈ T.final ∧ (𝒯').psi i P = y.2 := by
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  show (open Classical in if h : ∃ x ∈ P, x.1 ∈ T.final then (Classical.choose h).2 else []) = _
  exact dite_eq_left_of_eq_true (eq_true h)

/-! ### One step of the invariant -/

section Step

variable {w : List α} {a : α} {o : List β} {q : Fin k → Set (Q × List β)}

/-- Every run on `w ++ [a]` ending in `𝒞(Q_i)` is produced either by `τ_i`, or by the
separator channel followed by an `ε`-run. -/
theorem run_snoc_decomp (hT : T.IsSeparator part) (hR : ∀ x ∈ T.run w, o <+: x.2)
    (hq : ∀ i, q i = proj part o (T.run w) i) {x : Q × List β} (hx : x ∈ T.run (w ++ [a]))
    {i : Fin k} (hi : x.1 ∈ comp part i) :
    ∃ d, x.2 = o ++ d ∧ ((x.1, d) ∈ T.compStep part i (q i) a ∨
      ∃ r e d₁ d₂, e ∈ sepX part ∧ (e, d₁) ∈ T.compStep part r (q r) a ∧ d = d₁ ++ d₂ ∧
        T.Star e [] d₂ x.1) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨y, z, o₁, o₂, o₃, hout, hsy, hyz, hzx⟩ := Star.snoc_iff.mp hsx
  obtain ⟨d₀, rfl⟩ := hR (y, o₁) ⟨s, hs, hsy⟩
  have hyR : (y, o ++ d₀) ∈ T.run w := ⟨s, hs, hsy⟩
  have hyz' : T.Star y [a] o₂ z := Star.single hyz
  by_cases hyi : y ∈ comp part i
  · refine ⟨d₀ ++ o₂ ++ o₃, by rw [hout]; simp,
      Or.inl ⟨hi, (y, d₀), ?_, o₂ ++ o₃, hyz'.trans_eps hzx, by simp⟩⟩
    rw [hq]; exact ⟨hyi, hyR⟩
  · obtain ⟨r, hr⟩ : ∃ r, part y = some r := by
      rcases h : part y with _ | r
      · exact absurd (Or.inl h) hyi
      · exact ⟨r, rfl⟩
    have hri : r ≠ i := by rintro rfl; exact hyi (Or.inr hr)
    obtain ⟨e, he, v₁, v₂, rfl, hze, hex⟩ :=
      exists_sep_of_eps hT hzx (mem_comp_of_delta hT hyz hr) hi hri
    refine ⟨d₀ ++ o₂ ++ v₁ ++ v₂, by rw [hout]; simp, Or.inr ⟨r, e, d₀ ++ o₂ ++ v₁, v₂, he,
      ⟨sepX_subset_comp r he, (y, d₀), ?_, o₂ ++ v₁, hyz'.trans_eps hze, by simp⟩, rfl, hex⟩⟩
    rw [hq]; exact ⟨Or.inr hr, hyR⟩

theorem compStep_sound (hq : ∀ i, q i = proj part o (T.run w) i) {i : Fin k}
    {x : Q × List β} (hx : x ∈ T.compStep part i (q i) a) :
    (x.1, o ++ x.2) ∈ T.run (w ++ [a]) := by
  obtain ⟨-, p, hp, v, hpx, hx2⟩ := hx
  rw [hq] at hp
  obtain ⟨-, s, hs, hsp⟩ := hp
  refine ⟨s, hs, ?_⟩
  show T.Star s (w ++ [a]) (o ++ x.2) x.1
  rw [hx2, ← List.append_assoc]
  exact hsp.trans hpx

theorem compClose_sound (hq : ∀ i, q i = proj part o (T.run w) i) {i : Fin k}
    {x : Q × List β} (hx : x ∈ T.compClose part i ((𝒯').deltaX q a).2) :
    (x.1, o ++ x.2) ∈ T.run (w ++ [a]) ∧
      ∃ r, ∃ e ∈ T.compStep part r (q r) a, e.2 <+: x.2 := by
  obtain ⟨-, e, he, v, hev, hx2⟩ := hx
  obtain ⟨r, her, -⟩ := (mem_deltaX_snd q a e).mp he
  obtain ⟨s, hs, hse⟩ := compStep_sound hq her
  refine ⟨⟨s, hs, ?_⟩, r, e, her, ⟨v, hx2.symm⟩⟩
  show T.Star s (w ++ [a]) (o ++ x.2) x.1
  rw [hx2, ← List.append_assoc]
  exact hse.trans_eps hev

theorem step_none (hT : T.IsSeparator part) (hR : ∀ x ∈ T.run w, o <+: x.2)
    (hq : ∀ i, q i = proj part o (T.run w) i) (h : (𝒯').olam q a = none) :
    T.run (w ++ [a]) = ∅ ∧ ∀ i, (𝒯').delta q a i = ∅ := by
  have hspec := olam_spec (T := T) (part := part) q a
  rw [h] at hspec
  have hempty : ∀ r x, x ∉ T.compStep part r (q r) a := fun r x hx => by
    have : x.2 ∈ (⋃ r, Prod.snd '' T.compStep part r (q r) a) :=
      Set.mem_iUnion.mpr ⟨r, x, hx, rfl⟩
    rw [show (⋃ r, Prod.snd '' T.compStep part r (q r) a) = ∅ from hspec] at this
    exact this
  refine ⟨Set.eq_empty_of_forall_notMem fun x hx => ?_, fun i => ?_⟩
  · obtain ⟨i, hi⟩ := exists_mem_comp (ι := Fin k) (part := part) x.1
    obtain ⟨d, -, h₁ | ⟨r, e, d₁, -, -, he, -⟩⟩ := run_snoc_decomp hT hR hq hx hi
    exacts [hempty i _ h₁, hempty r _ he]
  · rw [delta_eq]
    refine Set.eq_empty_of_forall_notMem ?_
    rintro _ ⟨y, hy | ⟨-, e, he, -⟩, -⟩
    · exact hempty i y hy
    · obtain ⟨r, her, -⟩ := (mem_deltaX_snd q a e).mp he
      exact hempty r e her

theorem step_some (hT : T.IsSeparator part) (hR : ∀ x ∈ T.run w, o <+: x.2)
    (hq : ∀ i, q i = proj part o (T.run w) i) {m : List β} (h : (𝒯').olam q a = some m) :
    (∀ x ∈ T.run (w ++ [a]), o ++ m <+: x.2) ∧
    (∀ i, (𝒯').delta q a i = proj part (o ++ m) (T.run (w ++ [a])) i) ∧
    (∀ c, (∀ x ∈ T.run (w ++ [a]), o ++ m ++ c <+: x.2) → c = []) := by
  have hspec := olam_spec (T := T) (part := part) q a
  rw [h] at hspec
  have hm : ∀ r x, x ∈ T.compStep part r (q r) a → m <+: x.2 := fun r x hx =>
    hspec.2.prefix (Set.mem_iUnion.mpr ⟨r, x, hx, rfl⟩)
  refine ⟨fun x hx => ?_, fun i => ?_, fun c hc => ?_⟩
  · -- every output on `w ++ [a]` starts with `o ++ m`
    obtain ⟨i, hi⟩ := exists_mem_comp (ι := Fin k) (part := part) x.1
    obtain ⟨d, hd, h₁ | ⟨r, e, d₁, d₂, -, he, rfl, -⟩⟩ := run_snoc_decomp hT hR hq hx hi
    · rw [hd]
      exact (List.prefix_append_right_inj o).mpr (hm i _ h₁)
    · rw [hd]
      exact (List.prefix_append_right_inj o).mpr ((hm r _ he).trans (List.prefix_append _ _))
  · ext x
    rw [delta_eq, h, Option.getD_some]
    constructor
    · -- soundness (`quasisubseq_inclusion_left`)
      rintro ⟨y, hy, rfl⟩
      have key : y.1 ∈ comp part i ∧ (y.1, o ++ y.2) ∈ T.run (w ++ [a]) ∧ m <+: y.2 := by
        rcases hy with hy | hy
        · exact ⟨hy.1, compStep_sound hq hy, hm i y hy⟩
        · obtain ⟨hR', r, e, he, hey⟩ := compClose_sound hq hy
          exact ⟨hy.1, hR', (hm r e he).trans hey⟩
      obtain ⟨hi, hrun, d, hd⟩ := key
      refine ⟨hi, ?_⟩
      show (y.1, o ++ m ++ lquot m y.2) ∈ _
      rw [← hd, lquot_append, List.append_assoc, hd]
      exact hrun
    · -- completeness (`quasisubseq_inclusion_right`)
      rintro ⟨hi, hx⟩
      obtain ⟨d, hd, h₁ | ⟨r, e, d₁, d₂, he, her, hdd, hex⟩⟩ := run_snoc_decomp hT hR hq hx hi
      · have : d = m ++ x.2 := by simpa using hd.symm
        subst this
        exact ⟨(x.1, m ++ x.2), Or.inl h₁, by simp [lquot_append]⟩
      · have : d = m ++ x.2 := by simpa using hd.symm
        subst this
        refine ⟨(x.1, d₁ ++ d₂), Or.inr ⟨hi, (e, d₁), (mem_deltaX_snd q a _).mpr ⟨r, her, he⟩,
          d₂, hex, rfl⟩, ?_⟩
        simp [← hdd, lquot_append]
  · -- `o ++ m` is the longest common prefix of the outputs on `w ++ [a]`
    have : m ++ c <+: m := by
      refine (hspec.2 (m ++ c)).mp fun u hu => ?_
      obtain ⟨r, x, hx, rfl⟩ := Set.mem_iUnion.mp hu
      have := hc _ (compStep_sound hq hx)
      rwa [List.append_assoc, List.prefix_append_right_inj] at this
    have := this.length_le
    simp only [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)

end Step

/-! ### The invariant -/

variable (T part) in
/-- The invariant of `δ*(s, w)` and `λ*(s, w)`. -/
def Inv (w : List α) : Prop :=
  ((𝒯').lamStar (𝒯').start w = none →
      T.run w = ∅ ∧ ∀ i, (𝒯').deltaStar (𝒯').start w i = ∅) ∧
  ∀ o, (𝒯').lamStar (𝒯').start w = some o →
      (∀ x ∈ T.run w, o <+: x.2) ∧
      (∀ i, (𝒯').deltaStar (𝒯').start w i = proj part o (T.run w) i) ∧
      (w ≠ [] → ∀ c, (∀ x ∈ T.run w, o ++ c <+: x.2) → c = [])

theorem run_snoc_empty {w : List α} (h : T.run w = ∅) (a : α) : T.run (w ++ [a]) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x ⟨s, hs, hsx⟩ => ?_
  obtain ⟨y, -, o₁, -, -, -, hsy, -⟩ := Star.snoc_iff.mp hsx
  have : (y, o₁) ∈ T.run w := ⟨s, hs, hsy⟩
  rw [h] at this
  exact this

theorem inv_quasiSubseq (hT : T.IsSeparator part) (w : List α) : Inv T part w := by
  unfold Inv
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨fun h => by simp [QSFST.lamStar] at h, fun o ho => ?_⟩
    simp only [QSFST.lamStar, Option.some.injEq] at ho
    subst ho
    refine ⟨fun x _ => List.nil_prefix, fun i => ?_, fun h => absurd rfl h⟩
    ext x
    simp only [QDFA.deltaStar_nil]
    constructor
    · rintro ⟨hi, p, ⟨hs, hp⟩, v, hpx, hx⟩
      simp only [Set.mem_singleton_iff] at hp
      refine ⟨hi, p.1, hs, ?_⟩
      show T.Star p.1 [] ([] ++ x.2) x.1
      rw [hx, hp]; simpa using hpx
    · rintro ⟨hi, s, hs, hsx⟩
      exact ⟨hi, (s, []), ⟨hs, rfl⟩, x.2, by simpa using hsx, by simp⟩
  | append_singleton w a ih =>
    have hL := (𝒯').lamStar_append_singleton (𝒯').start w a
    rw [QDFA.deltaStar_append_singleton]
    rcases hw : (𝒯').lamStar (𝒯').start w with _ | o
    · -- no runs on `w`
      obtain ⟨hR0, hq0⟩ := ih.1 hw
      have hq : ∀ i, (𝒯').deltaStar (𝒯').start w i = proj part [] (T.run w) i := fun i => by
        rw [hq0, hR0]; ext x; simp [proj]
      have hR : ∀ x ∈ T.run w, ([] : List β) <+: x.2 := fun _ _ => List.nil_prefix
      have hrun := run_snoc_empty hR0 a
      rw [hw, Option.bind_none] at hL
      refine ⟨fun _ => ⟨hrun, fun i => ?_⟩, fun o ho => by rw [hL] at ho; cases ho⟩
      rcases hm : (𝒯').olam ((𝒯').deltaStar (𝒯').start w) a with _ | m
      · exact (step_none hT hR hq hm).2 i
      · rw [(step_some hT hR hq hm).2.1 i, hrun]; ext x; simp [proj]
    · obtain ⟨hR, hq, -⟩ := ih.2 o hw
      rw [hw, Option.bind_some] at hL
      rcases hm : (𝒯').olam ((𝒯').deltaStar (𝒯').start w) a with _ | m
      · rw [hm, Option.map_none] at hL
        exact ⟨fun _ => step_none hT hR hq hm, fun o' ho' => by rw [hL] at ho'; cases ho'⟩
      · rw [hm, Option.map_some] at hL
        refine ⟨fun h => (by rw [hL] at h; cases h), fun o' ho' => ?_⟩
        rw [hL, Option.some.injEq] at ho'
        subst ho'
        obtain ⟨h₁, h₂, h₃⟩ := step_some hT hR hq hm
        exact ⟨h₁, h₂, fun _ => h₃⟩

/-- The central invariant (Lemmas `quasisubseq_inclusion_right/left`): if `λ*(s, w) = o`, then
`δ*(s, w)ⁱ = {⟨p, d⟩ | p ∈ 𝒞(Q_i), ∃ s ∈ S, ⟨s, w, o·d, p⟩ ∈ Δ*}`. -/
theorem deltaStar_quasiSubseq (hT : T.IsSeparator part) {w : List α} {o : List β}
    (h : (𝒯').lamStar (𝒯').start w = some o) (i : Fin k) :
    (𝒯').deltaStar (𝒯').start w i = proj part o (T.run w) i :=
  ((inv_quasiSubseq hT w).2 o h).2.1 i

/-! ### The recognized relation -/

/-- `𝓡_{T'} ⊆ 𝓡_T`, for any separated `T`. -/
theorem quasiSubseq_relation_subset (hT : T.IsSeparator part) :
    (𝒯').relation ⊆ T.relation := by
  rintro ⟨w, v⟩ ⟨i, hfin, o, ho, hv⟩
  simp only at hfin ho hv
  obtain ⟨y, hy, hyF, hpsi⟩ := psi_spec (T := T) (part := part) i _ hfin
  rw [hv, hpsi]
  rw [deltaStar_quasiSubseq hT ho] at hy
  obtain ⟨-, s, hs, hsy⟩ := hy
  exact ⟨s, hs, y.1, hyF, hsy⟩

/-- Theorem (§4.4): for a functional separated transducer, `𝓡_{T'} = 𝓕_T`. -/
theorem quasiSubseq_relation (hT : T.IsSeparator part) (hF : T.IsFunctional) :
    (𝒯').relation = T.relation := by
  refine (quasiSubseq_relation_subset hT).antisymm ?_
  rintro ⟨w, v⟩ ⟨s, hs, f, hf, hsf⟩
  have hfv : (f, v) ∈ T.run w := ⟨s, hs, hsf⟩
  obtain ⟨o, ho⟩ : ∃ o, (𝒯').lamStar (𝒯').start w = some o := by
    rcases h : (𝒯').lamStar (𝒯').start w with _ | o
    · have := ((inv_quasiSubseq hT w).1 h).1
      rw [this] at hfv; exact absurd hfv (Set.notMem_empty _)
    · exact ⟨o, rfl⟩
  obtain ⟨hR, hq, -⟩ := (inv_quasiSubseq hT w).2 o ho
  obtain ⟨d, rfl⟩ := hR _ hfv
  obtain ⟨i, hi⟩ := exists_mem_comp (ι := Fin k) (part := part) f
  have hfin : (𝒯').deltaStar (𝒯').start w i ∈ (𝒯').final i :=
    ⟨(f, d), by rw [hq]; exact ⟨hi, hfv⟩, hf⟩
  obtain ⟨y, hy, hyF, hpsi⟩ := psi_spec (T := T) (part := part) i _ hfin
  rw [hq] at hy
  obtain ⟨-, s', hs', hsy⟩ := hy
  have := hF w _ _ ⟨s', hs', y.1, hyF, hsy⟩ ⟨s, hs, f, hf, hsf⟩
  exact ⟨i, hfin, o, ho, by rw [hpsi, this]⟩

/-! ### Lemma `quasisubseq_completion` -/

/-- Pending outputs of reachable states are bounded when `T` is trimmed and `𝓡_T` has bounded
variation. This is the core of Lemma `quasisubseq_completion`. -/
theorem pending_bounded [DecidableEq α] [Finite Q] (hT : T.IsSeparator part)
    (htrim : T.IsTrimmed) (hbv : BoundedVariation T.relation) :
    ∃ B, ∀ w o, w ≠ [] → (𝒯').lamStar (𝒯').start w = some o →
      ∀ x ∈ T.run w, x.2.length ≤ o.length + B := by
  choose f hf u v huv using fun q => (htrim q).2
  have := Fintype.ofFinite Q
  obtain ⟨K, hK⟩ := hbv (2 * Finset.univ.sup fun q => (u q).length)
  have hu : ∀ q, (u q).length ≤ Finset.univ.sup fun q => (u q).length :=
    fun q => Finset.le_sup (f := fun q => (u q).length) (Finset.mem_univ q)
  have hv : ∀ q, (v q).length ≤ Finset.univ.sup fun q => (v q).length :=
    fun q => Finset.le_sup (f := fun q => (v q).length) (Finset.mem_univ q)
  set V := Finset.univ.sup fun q => (v q).length
  refine ⟨K + V, fun w o hw ho x hx => ?_⟩
  obtain ⟨hR, -, hnorm⟩ := (inv_quasiSubseq hT w).2 o ho
  obtain ⟨d, hd⟩ := hR x hx
  by_contra hlt
  rw [← hd, List.length_append] at hlt
  obtain ⟨d₀, ds, rfl⟩ : ∃ d₀ ds, d = d₀ :: ds := by
    cases d with
    | nil => simp at hlt
    | cons d₀ ds => exact ⟨d₀, ds, rfl⟩
  -- some output on `w` does not continue with `d₀`
  obtain ⟨y, hy, hny⟩ : ∃ y ∈ T.run w, ¬ o ++ [d₀] <+: y.2 := by
    by_contra hall
    have : ∀ y ∈ T.run w, o ++ [d₀] <+: y.2 := fun y hy => by_contra fun h => hall ⟨y, hy, h⟩
    simpa using hnorm hw [d₀] this
  obtain ⟨d', hd'⟩ := hR y hy
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨s', hs', hsy⟩ := hy
  have h₁ : (w ++ u x.1, x.2 ++ v x.1) ∈ T.relation :=
    ⟨s, hs, f x.1, hf x.1, hsx.trans (huv x.1)⟩
  have h₂ : (w ++ u y.1, y.2 ++ v y.1) ∈ T.relation :=
    ⟨s', hs', f y.1, hf y.1, hsy.trans (huv y.1)⟩
  have hdist := hK _ _ _ _ h₁ h₂ (by
    have := dist_append_left_le w (u x.1) (u y.1)
    have := hu x.1; have := hu y.1
    omega)
  rw [← hd, ← hd', List.append_assoc, List.append_assoc, dist_append_left] at hdist
  have hvx := hv x.1
  have hvy := hv y.1
  cases d' with
  | nil =>
    have hl := (lcp_prefix_right (d₀ :: ds ++ v x.1) (v y.1)).length_le
    simp only [List.nil_append] at hdist hl
    unfold dist at hdist
    simp only [List.length_append, List.length_cons] at hdist hlt
    omega
  | cons e es =>
    have hne : d₀ ≠ e := by
      rintro rfl
      exact hny (by rw [← hd']; exact (List.prefix_append_right_inj o).mpr (by simp))
    unfold dist at hdist
    rw [List.cons_append, List.cons_append, lcp_cons_cons_of_ne hne] at hdist
    simp only [List.length_nil, List.length_cons, List.length_append] at hdist hlt
    omega

/-- Only finitely many states of `𝒯'` are reachable. -/
theorem reachable_quasiSubseq_finite [DecidableEq α] [Finite Q] [Finite β]
    (hT : T.IsSeparator part) (htrim : T.IsTrimmed) (hbv : BoundedVariation T.relation) :
    (reachable (𝒯').delta (𝒯').start).Finite := by
  obtain ⟨B, hB⟩ := pending_bounded hT htrim hbv
  let U : Set (Q × List β) := Set.univ ×ˢ {d | d.length ≤ B}
  have hU : U.Finite := Set.finite_univ.prod (List.finite_length_le β B)
  have hpi : (Set.pi Set.univ fun _ : Fin k => 𝒫 U).Finite := Set.Finite.pi fun _ => hU.powerset
  refine (((Set.finite_singleton (𝒯').start).union
    (Set.finite_singleton fun _ => ∅)).union hpi).subset ?_
  rintro p ⟨w, rfl⟩
  change (𝒯').deltaStar (𝒯').start w ∈ _
  by_cases hw : w = []
  · subst hw; exact Or.inl (Or.inl rfl)
  rcases ho : (𝒯').lamStar (𝒯').start w with _ | o
  · exact Or.inl (Or.inr (funext ((inv_quasiSubseq hT w).1 ho).2))
  · refine Or.inr (Set.mem_univ_pi.mpr fun i x hx => ?_)
    rw [deltaStar_quasiSubseq hT ho] at hx
    have := hB w o hw ho _ hx.2
    simp only [List.length_append] at this
    exact ⟨Set.mem_univ _, by show x.2.length ≤ B; omega⟩

/-- Lemma `quasisubseq_completion`: for a trimmed separated transducer whose relation has bounded
variation, the sequence `R^{(n)}` stabilizes at the set of reachable states. -/
theorem quasisubseq_completion [DecidableEq α] [Finite Q] [Finite β] (hT : T.IsSeparator part)
    (htrim : T.IsTrimmed) (hbv : BoundedVariation T.relation) :
    ∃ m, ∀ n ≥ m, reachR (𝒯').delta (𝒯').start n = reachR (𝒯').delta (𝒯').start (n + 1) ∧
      reachR (𝒯').delta (𝒯').start n = reachable (𝒯').delta (𝒯').start :=
  reachR_stabilizes (reachable_quasiSubseq_finite hT htrim hbv)

/-- Theorem (§4.4): every trimmed functional separated transducer whose function has bounded
variation has an equivalent quasi-subsequential transducer with finitely many reachable states. -/
theorem exists_quasiSubseq [DecidableEq α] [Finite Q] [Finite β] (hT : T.IsSeparator part)
    (htrim : T.IsTrimmed) (hF : T.IsFunctional) (hbv : BoundedVariation T.relation) :
    ∃ M : QSFST α β k (fun _ => Set (Q × List β)) (SepData β Q),
      M.relation = T.relation ∧ (reachable M.delta M.start).Finite :=
  ⟨𝒯', quasiSubseq_relation hT hF, reachable_quasiSubseq_finite hT htrim hbv⟩

end FST

end Sqdfsa
