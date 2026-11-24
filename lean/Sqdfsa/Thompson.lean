import Sqdfsa.PerComponent

/-!
# Separators in Thompson automata (thesis §3.2)

`thompson e` is the automaton built from a regular expression `e` by the construction of
Theorem `thompson` (Types 1–5 of the thesis). Its states are built structurally, so that the
states of the automaton of a subexpression embed into those of the whole automaton.

Algorithm `thompson_separator` walks down the expression tree, always into the larger child,
while the current subautomaton has more than `2|Q|/3` inner states. We model the walk as a
position `p : Pos e` in the expression tree (`descend`). The separator is
`X = {start, final}` of the subautomaton at `p`. The two blocks are its inner states (`Q_c \ X`)
and the states outside of it (`R`).

Results:
* `thompson_isSeparator`: `X` separates the two blocks (Propositions `thompson_sep_3`,
  `thompson_sep_6`).
* `ncard_thompsonSep_sepX`: `|X| = 2` (Proposition `thompson_sep_4`).
* `thompsonSep_block_le`: both blocks have at most `2|Q|/3` states (loop condition and
  Proposition `thompson_sep_5`).
* `descendSteps_le`: the walk takes at most `|Q|` steps (Proposition `thompson_sep_2`).
* `thompson_quasiDet_cost`: combined with the per-component algorithm, every regular expression
  can be quasi-determinized in `O(|Σ|·|Q|·2^{2|Q|/3})` time.

The planarity of the graphs of Thompson automata (first proposition of §3.2) is not
formalized: Mathlib has no theory of planar embeddings, and the result is only used to motivate
the use of separators.
-/

set_option linter.unusedSectionVars false

namespace Sqdfsa

variable {α : Type*}

/-! ### The Thompson construction -/

/-- States of the Thompson automaton. `false`/`true` in `Bool` are the new start/final state. -/
@[reducible] def TState : RegularExpression α → Type
  | .zero => Bool
  | .epsilon => Bool
  | .char _ => Bool
  | .comp a b => TState a ⊕ TState b
  | .plus a b => Bool ⊕ (TState a ⊕ TState b)
  | .star a => Bool ⊕ TState a

instance TState.finite : ∀ e : RegularExpression α, Finite (TState e)
  | .zero => inferInstanceAs (Finite Bool)
  | .epsilon => inferInstanceAs (Finite Bool)
  | .char _ => inferInstanceAs (Finite Bool)
  | .comp a b => have := TState.finite a; have := TState.finite b
    inferInstanceAs (Finite (TState a ⊕ TState b))
  | .plus a b => have := TState.finite a; have := TState.finite b
    inferInstanceAs (Finite (Bool ⊕ (TState a ⊕ TState b)))
  | .star a => have := TState.finite a; inferInstanceAs (Finite (Bool ⊕ TState a))

/-- The start state. -/
def tStart : ∀ e : RegularExpression α, TState e
  | .zero => false
  | .epsilon => false
  | .char _ => false
  | .comp a _ => .inl (tStart a)
  | .plus _ _ => .inl false
  | .star _ => .inl false

/-- The final state. -/
def tFinal : ∀ e : RegularExpression α, TState e
  | .zero => true
  | .epsilon => true
  | .char _ => true
  | .comp _ b => .inr (tFinal b)
  | .plus _ _ => .inl true
  | .star _ => .inl true

/-- Transitions mapped along a function on states. -/
def liftT {A B : Type*} (f : A → B) (t : A × Option α × A) : B × Option α × B :=
  (f t.1, t.2.1, f t.2.2)

/-- The transitions of the Thompson automaton. -/
def tDelta : ∀ e : RegularExpression α, Set (TState e × Option α × TState e)
  | .zero => ∅
  | .epsilon => {(false, none, true)}
  | .char c => {(false, some c, true)}
  | .comp a b =>
    liftT (Sum.inl : TState a → TState (.comp a b)) '' tDelta a ∪
      liftT (Sum.inr : TState b → TState (.comp a b)) '' tDelta b ∪
      {(.inl (tFinal a), none, .inr (tStart b))}
  | .plus a b =>
    liftT (fun x => .inr (.inl x) : TState a → TState (.plus a b)) '' tDelta a ∪
      liftT (fun x => .inr (.inr x) : TState b → TState (.plus a b)) '' tDelta b ∪
      {(.inl false, none, .inr (.inl (tStart a))), (.inl false, none, .inr (.inr (tStart b))),
        (.inr (.inl (tFinal a)), none, .inl true), (.inr (.inr (tFinal b)), none, .inl true)}
  | .star a =>
    liftT (Sum.inr : TState a → TState (.star a)) '' tDelta a ∪
      {(.inr (tFinal a), none, .inr (tStart a)), (.inr (tFinal a), none, .inl true),
        (.inl false, none, .inr (tStart a)), (.inl false, none, .inl true)}

/-- The Thompson automaton of `e`. -/
def thompson (e : RegularExpression α) : FSA α (TState e) :=
  ⟨{tStart e}, {tFinal e}, tDelta e⟩

/-- The number of states of the Thompson automaton. -/
def nstates : RegularExpression α → ℕ
  | .zero => 2
  | .epsilon => 2
  | .char _ => 2
  | .comp a b => nstates a + nstates b
  | .plus a b => nstates a + nstates b + 2
  | .star a => nstates a + 2

theorem two_le_nstates : ∀ e : RegularExpression α, 2 ≤ nstates e
  | .zero | .epsilon | .char _ => le_rfl
  | .comp a _ => le_trans (two_le_nstates a) (Nat.le_add_right _ _)
  | .plus _ _ => Nat.le_add_left _ _
  | .star _ => Nat.le_add_left _ _

theorem card_tState : ∀ e : RegularExpression α, Nat.card (TState e) = nstates e
  | .zero | .epsilon | .char _ => by
    show Nat.card Bool = 2
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  | .comp a b => by
    rw [nstates, ← card_tState a, ← card_tState b]
    exact Nat.card_sum
  | .plus a b => by
    rw [nstates, ← card_tState a, ← card_tState b]
    show Nat.card (Bool ⊕ (TState a ⊕ TState b)) = _
    rw [Nat.card_sum, Nat.card_sum, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    ring
  | .star a => by
    rw [nstates, ← card_tState a]
    show Nat.card (Bool ⊕ TState a) = _
    rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    ring

theorem tStart_ne_tFinal : ∀ e : RegularExpression α, tStart e ≠ tFinal e
  | .zero | .epsilon | .char _ => Bool.false_ne_true
  | .comp _ _ => Sum.inl_ne_inr
  | .plus _ _ => fun h => Bool.false_ne_true (Sum.inl_injective h)
  | .star _ => fun h => Bool.false_ne_true (Sum.inl_injective h)

/-! ### Positions in the expression tree -/

/-- A position in the expression tree of `e`: the subexpression the algorithm has descended to. -/
inductive Pos : RegularExpression α → Type _
  | here (e : RegularExpression α) : Pos e
  | compL {a b : RegularExpression α} : Pos a → Pos (.comp a b)
  | compR {a b : RegularExpression α} : Pos b → Pos (.comp a b)
  | plusL {a b : RegularExpression α} : Pos a → Pos (.plus a b)
  | plusR {a b : RegularExpression α} : Pos b → Pos (.plus a b)
  | star {a : RegularExpression α} : Pos a → Pos (.star a)

/-- The subexpression at a position. -/
def Pos.expr : {e : RegularExpression α} → Pos e → RegularExpression α
  | _, here e => e
  | _, compL p => p.expr
  | _, compR p => p.expr
  | _, plusL p => p.expr
  | _, plusR p => p.expr
  | _, star p => p.expr

/-- The embedding of the states of the subautomaton at a position. -/
def Pos.emb : {e : RegularExpression α} → (p : Pos e) → TState p.expr → TState e
  | _, here _ => id
  | _, compL p => fun x => .inl (p.emb x)
  | _, compR p => fun x => .inr (p.emb x)
  | _, plusL p => fun x => .inr (.inl (p.emb x))
  | _, plusR p => fun x => .inr (.inr (p.emb x))
  | _, star p => fun x => .inr (p.emb x)

theorem Pos.emb_injective : ∀ {e : RegularExpression α} (p : Pos e), Function.Injective p.emb
  | _, here _ => Function.injective_id
  | _, compL p => fun _ _ h => p.emb_injective (Sum.inl_injective h)
  | _, compR p => fun _ _ h => p.emb_injective (Sum.inr_injective h)
  | _, plusL p => fun _ _ h => p.emb_injective (Sum.inl_injective (Sum.inr_injective h))
  | _, plusR p => fun _ _ h => p.emb_injective (Sum.inr_injective (Sum.inr_injective h))
  | _, star p => fun _ _ h => p.emb_injective (Sum.inr_injective h)

/-- `x` is an inner state: neither the start nor the final state. -/
def Inner {e : RegularExpression α} (x : TState e) : Prop := x ≠ tStart e ∧ x ≠ tFinal e

/-- Inner states of a subautomaton are inner states of the whole automaton. -/
theorem Pos.emb_inner : ∀ {e : RegularExpression α} (p : Pos e) {u : TState p.expr},
    Inner u → Inner (p.emb u)
  | _, here _, _, h => h
  | _, compL p, _, h => by
    have := p.emb_inner h
    exact ⟨fun h' => this.1 (Sum.inl_injective h'), fun h' => Sum.inl_ne_inr h'⟩
  | _, compR p, _, h => by
    have := p.emb_inner h
    exact ⟨fun h' => Sum.inr_ne_inl h', fun h' => this.2 (Sum.inr_injective h')⟩
  | _, plusL _, _, _ => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl⟩
  | _, plusR _, _, _ => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl⟩
  | _, star _, _, _ => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl⟩

/-- Locality: a transition touching an inner state of the subautomaton at `p` is a transition of
that subautomaton. -/
theorem Pos.local : ∀ {e : RegularExpression α} (p : Pos e) {t : TState e × Option α × TState e},
    t ∈ tDelta e → (∃ u, Inner u ∧ t.1 = p.emb u) ∨ (∃ v, Inner v ∧ t.2.2 = p.emb v) →
      ∃ t' ∈ tDelta p.expr, t = liftT p.emb t'
  | _, here _, t, ht, _ => ⟨t, ht, rfl⟩
  | _, compL (a := a) (b := b) p, t, ht, h => by
    rcases ht with (⟨t₀, h₀, rfl⟩ | ⟨t₀, h₀, rfl⟩) | rfl
    · have h' : (∃ u, Inner u ∧ t₀.1 = p.emb u) ∨ (∃ v, Inner v ∧ t₀.2.2 = p.emb v) := by
        rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
        · exact Or.inl ⟨u, hu, Sum.inl_injective e⟩
        · exact Or.inr ⟨v, hv, Sum.inl_injective e⟩
      obtain ⟨t', ht', rfl⟩ := p.local h₀ h'
      exact ⟨t', ht', rfl⟩
    · rcases h with ⟨u, -, e⟩ | ⟨v, -, e⟩ <;> exact absurd e Sum.inr_ne_inl
    · rcases h with ⟨u, hu, e⟩ | ⟨v, -, e⟩
      · exact absurd (Sum.inl_injective e).symm (p.emb_inner hu).2
      · exact absurd e Sum.inr_ne_inl
  | _, compR (a := a) (b := b) p, t, ht, h => by
    rcases ht with (⟨t₀, h₀, rfl⟩ | ⟨t₀, h₀, rfl⟩) | rfl
    · rcases h with ⟨u, -, e⟩ | ⟨v, -, e⟩ <;> exact absurd e Sum.inl_ne_inr
    · have h' : (∃ u, Inner u ∧ t₀.1 = p.emb u) ∨ (∃ v, Inner v ∧ t₀.2.2 = p.emb v) := by
        rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
        · exact Or.inl ⟨u, hu, Sum.inr_injective e⟩
        · exact Or.inr ⟨v, hv, Sum.inr_injective e⟩
      obtain ⟨t', ht', rfl⟩ := p.local h₀ h'
      exact ⟨t', ht', rfl⟩
    · rcases h with ⟨u, -, e⟩ | ⟨v, hv, e⟩
      · exact absurd e Sum.inl_ne_inr
      · exact absurd (Sum.inr_injective e).symm (p.emb_inner hv).1
  | _, plusL (a := a) (b := b) p, t, ht, h => by
    rcases ht with (⟨t₀, h₀, rfl⟩ | ⟨t₀, h₀, rfl⟩) | ht
    · have h' : (∃ u, Inner u ∧ t₀.1 = p.emb u) ∨ (∃ v, Inner v ∧ t₀.2.2 = p.emb v) := by
        rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
        · exact Or.inl ⟨u, hu, Sum.inl_injective (Sum.inr_injective e)⟩
        · exact Or.inr ⟨v, hv, Sum.inl_injective (Sum.inr_injective e)⟩
      obtain ⟨t', ht', rfl⟩ := p.local h₀ h'
      exact ⟨t', ht', rfl⟩
    · rcases h with ⟨u, -, e⟩ | ⟨v, -, e⟩ <;>
        exact absurd (Sum.inr_injective e) Sum.inr_ne_inl
    · exfalso
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
      · -- only transitions from the final state of the subautomaton remain
        rcases ht with rfl | rfl | rfl | rfl <;> simp [Pos.emb] at e
        exact (p.emb_inner hu).2 e.symm
      · -- only transitions into the start state of the subautomaton remain
        rcases ht with rfl | rfl | rfl | rfl <;> simp [Pos.emb] at e
        exact (p.emb_inner hv).1 e.symm
  | _, plusR (a := a) (b := b) p, t, ht, h => by
    rcases ht with (⟨t₀, h₀, rfl⟩ | ⟨t₀, h₀, rfl⟩) | ht
    · rcases h with ⟨u, -, e⟩ | ⟨v, -, e⟩ <;>
        exact absurd (Sum.inr_injective e) Sum.inl_ne_inr
    · have h' : (∃ u, Inner u ∧ t₀.1 = p.emb u) ∨ (∃ v, Inner v ∧ t₀.2.2 = p.emb v) := by
        rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
        · exact Or.inl ⟨u, hu, Sum.inr_injective (Sum.inr_injective e)⟩
        · exact Or.inr ⟨v, hv, Sum.inr_injective (Sum.inr_injective e)⟩
      obtain ⟨t', ht', rfl⟩ := p.local h₀ h'
      exact ⟨t', ht', rfl⟩
    · exfalso
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
      · -- only transitions from the final state of the subautomaton remain
        rcases ht with rfl | rfl | rfl | rfl <;> simp [Pos.emb] at e
        exact (p.emb_inner hu).2 e.symm
      · -- only transitions into the start state of the subautomaton remain
        rcases ht with rfl | rfl | rfl | rfl <;> simp [Pos.emb] at e
        exact (p.emb_inner hv).1 e.symm
  | _, star (a := a) p, t, ht, h => by
    rcases ht with ⟨t₀, h₀, rfl⟩ | ht
    · have h' : (∃ u, Inner u ∧ t₀.1 = p.emb u) ∨ (∃ v, Inner v ∧ t₀.2.2 = p.emb v) := by
        rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
        · exact Or.inl ⟨u, hu, Sum.inr_injective e⟩
        · exact Or.inr ⟨v, hv, Sum.inr_injective e⟩
      obtain ⟨t', ht', rfl⟩ := p.local h₀ h'
      exact ⟨t', ht', rfl⟩
    · exfalso
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases h with ⟨u, hu, e⟩ | ⟨v, hv, e⟩
      · -- only transitions from the final state of the subautomaton remain
        rcases ht with rfl | rfl | rfl | rfl <;> simp [Pos.emb] at e
        all_goals exact (p.emb_inner hu).2 e.symm
      · -- only transitions into the start state of the subautomaton remain
        rcases ht with rfl | rfl | rfl | rfl <;> simp [Pos.emb] at e
        all_goals exact (p.emb_inner hv).1 e.symm

/-! ### The separator induced by a position -/

variable {r : RegularExpression α}

/-- The partition induced by a position `p`: `none` for `X = {start, final}` of the
subautomaton at `p`, `some 0` for its inner states (`Q_c \ X`), `some 1` for the states
outside of it (`R`). -/
noncomputable def sepPart (p : Pos r) (x : TState r) : Option (Fin 2) :=
  open Classical in
  if x = p.emb (tStart p.expr) ∨ x = p.emb (tFinal p.expr) then none
  else if x ∈ Set.range p.emb then some 0 else some 1

theorem sepPart_eq_none (p : Pos r) (x : TState r) :
    sepPart p x = none ↔ x = p.emb (tStart p.expr) ∨ x = p.emb (tFinal p.expr) := by
  unfold sepPart; split_ifs <;> simp_all

theorem sepPart_eq_zero (p : Pos r) (x : TState r) :
    sepPart p x = some 0 ↔ ∃ u, Inner u ∧ x = p.emb u := by
  unfold sepPart
  split_ifs with h₁ h₂
  · simp only [false_iff]
    rintro ⟨u, hu, rfl⟩
    rcases h₁ with h | h
    · exact hu.1 (p.emb_injective h)
    · exact hu.2 (p.emb_injective h)
  · simp only [true_iff]
    obtain ⟨u, rfl⟩ := h₂
    exact ⟨u, ⟨fun h => h₁ (Or.inl (by rw [h])), fun h => h₁ (Or.inr (by rw [h]))⟩, rfl⟩
  · simp only [Option.some.injEq, Fin.reduceEq, false_iff]
    rintro ⟨u, -, rfl⟩
    exact h₂ ⟨u, rfl⟩

theorem sepPart_eq_one (p : Pos r) (x : TState r) :
    sepPart p x = some 1 ↔ x ∉ Set.range p.emb := by
  unfold sepPart
  split_ifs with h₁ h₂
  · simp only [false_iff, not_not]
    rcases h₁ with h | h <;> exact ⟨_, h.symm⟩
  · simp only [Option.some.injEq, Fin.reduceEq, false_iff, not_not]; exact h₂
  · simp only [true_iff]; exact h₂

/-- Propositions `thompson_sep_3` and `thompson_sep_6`: no transition joins an inner state of
the subautomaton at `p` with a state outside of it. -/
theorem thompson_isSeparator (p : Pos r) : (thompson r).IsSeparator (sepPart p) := by
  intro q a q' i j hd hi hj
  have hin : ∀ {x : TState r}, sepPart p x = some 0 → ∃ u, Inner u ∧ x = p.emb u :=
    fun h => (sepPart_eq_zero p _).mp h
  have hout : ∀ {x : TState r}, sepPart p x = some 1 → x ∉ Set.range p.emb :=
    fun h => (sepPart_eq_one p _).mp h
  fin_cases i <;> fin_cases j
  · rfl
  · obtain ⟨t', -, ht'⟩ := p.local hd (Or.inl (hin hi))
    exact absurd ⟨t'.2.2, by rw [show q' = _ from congrArg (fun t => t.2.2) ht']; rfl⟩ (hout hj)
  · obtain ⟨t', -, ht'⟩ := p.local hd (Or.inr (hin hj))
    exact absurd ⟨t'.1, by rw [show q = _ from congrArg (fun t => t.1) ht']; rfl⟩ (hout hi)
  · rfl

/-- Proposition `thompson_sep_4`: `|X| = 2`. -/
theorem ncard_thompsonSep_sepX (p : Pos r) : (sepX (sepPart p)).ncard = 2 := by
  have : sepX (sepPart p) = {p.emb (tStart p.expr), p.emb (tFinal p.expr)} := by
    ext x; simp [sepX, sepPart_eq_none]
  rw [this, Set.ncard_pair]
  exact fun h => tStart_ne_tFinal _ (p.emb_injective h)

theorem ncard_block_zero (p : Pos r) :
    {x | sepPart p x = some 0}.ncard = nstates p.expr - 2 := by
  have h : {x | sepPart p x = some 0} = p.emb '' {u | Inner u} := by
    ext x; simp only [Set.mem_ofPred_eq, sepPart_eq_zero, Set.mem_image]
    exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩
  have h' : {u : TState p.expr | Inner u} = Set.univ \ {tStart p.expr, tFinal p.expr} := by
    ext u; simp [Inner]
  rw [h, Set.ncard_image_of_injective _ p.emb_injective, h',
    Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, Set.ncard_pair (tStart_ne_tFinal _),
    card_tState]

theorem ncard_block_one (p : Pos r) :
    {x | sepPart p x = some 1}.ncard = nstates r - nstates p.expr := by
  have h : {x | sepPart p x = some 1} = (Set.range p.emb)ᶜ := by
    ext x; simp [sepPart_eq_one]
  have hr : (Set.range p.emb).ncard = nstates p.expr := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ p.emb_injective, Set.ncard_univ,
      card_tState]
  have := Set.ncard_add_ncard_compl (Set.range p.emb)
  rw [hr, card_tState] at this
  rw [h]; omega

/-! ### Algorithm `thompson_separator` -/

/-- Algorithm `thompson_separator` as a descent in the expression tree: while the current
subautomaton has more than `2N/3` inner states, descend into the larger child (Types 3 and 4)
or the only child (Type 5). Types 1 and 2 have no inner states. -/
def descend (N : ℕ) : ∀ e : RegularExpression α, Pos e
  | .comp a b =>
    if 3 * (nstates (.comp a b) - 2) ≤ 2 * N then .here _
    else if nstates b ≤ nstates a then .compL (descend N a) else .compR (descend N b)
  | .plus a b =>
    if 3 * (nstates (.plus a b) - 2) ≤ 2 * N then .here _
    else if nstates b ≤ nstates a then .plusL (descend N a) else .plusR (descend N b)
  | .star a =>
    if 3 * (nstates (.star a) - 2) ≤ 2 * N then .here _ else .star (descend N a)
  | e => .here e

/-- The number of iterations of the loop of Algorithm `thompson_separator`. -/
def descendSteps (N : ℕ) : RegularExpression α → ℕ
  | .comp a b =>
    if 3 * (nstates (.comp a b) - 2) ≤ 2 * N then 0
    else if nstates b ≤ nstates a then descendSteps N a + 1 else descendSteps N b + 1
  | .plus a b =>
    if 3 * (nstates (.plus a b) - 2) ≤ 2 * N then 0
    else if nstates b ≤ nstates a then descendSteps N a + 1 else descendSteps N b + 1
  | .star a =>
    if 3 * (nstates (.star a) - 2) ≤ 2 * N then 0 else descendSteps N a + 1
  | _ => 0

/-- Proposition `thompson_sep_2`: the loop executes at most `|Q|` iterations. -/
theorem descendSteps_le (N : ℕ) : ∀ e : RegularExpression α, descendSteps N e ≤ nstates e
  | .zero | .epsilon | .char _ => Nat.zero_le _
  | .comp a b => by
    have := descendSteps_le N a; have := descendSteps_le N b
    have := two_le_nstates a; have := two_le_nstates b
    rw [descendSteps]
    by_cases h₁ : 3 * (nstates (.comp a b) - 2) ≤ 2 * N
    · simp only [h₁, ↓reduceIte]; exact Nat.zero_le _
    · simp only [h₁, ↓reduceIte]; simp only [nstates]; split_ifs <;> omega
  | .plus a b => by
    have := descendSteps_le N a; have := descendSteps_le N b
    rw [descendSteps]
    by_cases h₁ : 3 * (nstates (.plus a b) - 2) ≤ 2 * N
    · simp only [h₁, ↓reduceIte]; exact Nat.zero_le _
    · simp only [h₁, ↓reduceIte]; simp only [nstates]; split_ifs <;> omega
  | .star a => by
    have := descendSteps_le N a
    rw [descendSteps]
    by_cases h₁ : 3 * (nstates (.star a) - 2) ≤ 2 * N
    · simp only [h₁, ↓reduceIte]; exact Nat.zero_le _
    · simp only [h₁, ↓reduceIte]; simp only [nstates]; omega

/-- The loop condition and Proposition `thompson_sep_5`: if at most `2N/3` states lie outside
of `e`, then after the descent both blocks have at most `2N/3` states. -/
theorem descend_bounds (N : ℕ) : ∀ e : RegularExpression α, nstates e ≤ N →
    3 * (N - nstates e) ≤ 2 * N →
      3 * (nstates (descend N e).expr - 2) ≤ 2 * N ∧
        3 * (N - nstates (descend N e).expr) ≤ 2 * N
  | .zero, _, h | .epsilon, _, h | .char _, _, h => ⟨by simp [descend, Pos.expr, nstates], h⟩
  | .comp a b, hN, h => by
    have := two_le_nstates a; have := two_le_nstates b
    simp only [nstates] at hN h
    simp only [descend]
    split_ifs with h₁ h₂
    · exact ⟨h₁, by simpa [Pos.expr, nstates] using h⟩
    · simp only [nstates] at h₁
      exact descend_bounds N a (by omega) (by omega)
    · simp only [nstates] at h₁
      exact descend_bounds N b (by omega) (by omega)
  | .plus a b, hN, h => by
    have := two_le_nstates a; have := two_le_nstates b
    simp only [nstates] at hN h
    simp only [descend]
    split_ifs with h₁ h₂
    · exact ⟨h₁, by simpa [Pos.expr, nstates] using h⟩
    · simp only [nstates] at h₁
      exact descend_bounds N a (by omega) (by omega)
    · simp only [nstates] at h₁
      exact descend_bounds N b (by omega) (by omega)
  | .star a, hN, h => by
    have := two_le_nstates a
    simp only [nstates] at hN h
    simp only [descend]
    split_ifs with h₁
    · exact ⟨h₁, by simpa [Pos.expr, nstates] using h⟩
    · simp only [nstates] at h₁
      exact descend_bounds N a (by omega) (by omega)

/-- The partition computed by Algorithm `thompson_separator`. -/
noncomputable def thompsonSep (r : RegularExpression α) : TState r → Option (Fin 2) :=
  sepPart (descend (nstates r) r)

/-- Theorem (§3.2): the Thompson automaton of every regular expression has a separator `X` with
`|X| = 2` whose two blocks have at most `2|Q|/3` states each, found in at most `|Q|`
iterations. -/
theorem thompson_separator (r : RegularExpression α) :
    (thompson r).IsSeparator (thompsonSep r) ∧ (sepX (thompsonSep r)).ncard = 2 ∧
      (∀ i, 3 * {x | thompsonSep r x = some i}.ncard ≤ 2 * nstates r) ∧
      descendSteps (nstates r) r ≤ nstates r := by
  obtain ⟨h₀, h₁⟩ := descend_bounds (nstates r) r le_rfl (by simp)
  refine ⟨thompson_isSeparator _, ncard_thompsonSep_sepX _, fun i => ?_, descendSteps_le _ _⟩
  fin_cases i
  · simpa [thompsonSep, ncard_block_zero] using h₀
  · simpa [thompsonSep, ncard_block_one] using h₁

/-! ### Quasi-determinization of Thompson automata -/

/-- Quasi-determinization of regular expressions: the per-component algorithm, applied to the
Thompson automaton of `r` with the separator of Algorithm `thompson_separator`, produces an
equivalent quasi-deterministic automaton in `O(|Σ|·|Q|·2^{2|Q|/3})` time, compared with up to
`2^{|Q|}` states for the subset construction. -/
theorem thompson_quasiDet (r : RegularExpression α) :
    ((thompson r).perComponent (thompsonSep r)).language = (thompson r).language ∧
      FSA.perComponentCost (Nat.card α) 2 (nstates r)
          (fun i => ((thompson r).compClosure (thompsonSep r) i).ncard)
          (fun i => ((thompson r).tauImage (thompsonSep r) i).ncard) ≤
        24 * (Nat.card α + 5) * nstates r * 2 ^ (2 * nstates r / 3) := by
  obtain ⟨hsep, hX, hblock, -⟩ := thompson_separator r
  refine ⟨FSA.perComponent_language hsep, ?_⟩
  have hc := FSA.perComponentCost_le (A := thompson r) (part := thompsonSep r)
  rw [hX, card_tState] at hc
  refine hc.trans ?_
  have hpow : ∀ i : Fin 2, 2 ^ {q | thompsonSep r q = some i}.ncard ≤ 2 ^ (2 * nstates r / 3) :=
    fun i => Nat.pow_le_pow_right (by norm_num) (by have := hblock i; omega)
  have hsum : ∑ i : Fin 2, 2 ^ {q | thompsonSep r q = some i}.ncard ≤
      2 * 2 ^ (2 * nstates r / 3) := by
    rw [Fin.sum_univ_two]; have := hpow 0; have := hpow 1; omega
  calc 3 * (Nat.card α + 2 ^ 2 + 1) * nstates r * 2 ^ 2 *
        ∑ i : Fin 2, 2 ^ {q | thompsonSep r q = some i}.ncard
      ≤ 3 * (Nat.card α + 2 ^ 2 + 1) * nstates r * 2 ^ 2 * (2 * 2 ^ (2 * nstates r / 3)) :=
        Nat.mul_le_mul_left _ hsum
    _ = 24 * (Nat.card α + 5) * nstates r * 2 ^ (2 * nstates r / 3) := by ring

end Sqdfsa
