# Lean formalization

Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`) formalization of
*Separators for Quasi-Determinization of Finite-State Devices*.

```sh
lake exe cache get   # first time only: download prebuilt Mathlib
lake build
```

No `sorry`s; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Map from thesis to Lean

| Thesis | Lean | File |
|---|---|---|
| Prop. `left_word_factor` | `left_word_factor` | `Words.lean` |
| FSA, `Δ*` | `FSA`, `FSA.Star` | `FSA.lean` |
| Prop. path ⇔ `Δ*` | `FSA.star_iff_exists_path` (paths = Mathlib `εNFA.IsPath`) | `FSA.lean` |
| `𝓛_A` | `FSA.language`, `= toεNFA.accepts` (`language_eq_accepts`) | `FSA.lean` |
| Thm. Rabin–Scott | `FSA.rabin_scott` (via Mathlib `NFA.toDFA_correct`) | `FSA.lean` |
| Graph `𝒢_A`, graph separator | `FSA.graphEdges` (edges as `Sym2`), `IsGraphSeparator` | `FSA.lean` |
| Separator in an FSA, `k`-separated | `FSA.IsSeparator`, `FSA.IsKSeparated` | `Separated.lean` |
| Prop. graph separator ⇒ FSA separator | `FSA.isSeparator_of_graph` | `Separated.lean` |
| Prop. `small_delta` | `FSA.small_delta` | `Separated.lean` |
| Prop. runs between components cross `X` | `FSA.exists_sep_of_star` | `Separated.lean` |
| `Δᵢ_ε` and its three propositions | `FSA.compClose`, `exists_of_compClose`, `compClose_compClose_inter_subset`, `compClose_eq_of_ne` | `Separated.lean` |
| `k`-separated QDFA, `δ_x`, `δ`, `δ*`, `𝓛` | `QDFA`, `deltaX`, `delta`, `deltaStar`, `language` | `QDFA.lean` |
| Prop. path ⇔ `δ*` | `QDFA.isPath_iff` | `QDFA.lean` |
| Lemmas `quasidet_equiv_left/right`, Thm. QDFA ≡ DFA | `QDFA.toDFA_accepts`, `QDFA.ofDFA_language`, `qdfa_iff_dfa` | `QDFA.lean` |
| Alg. `qdfsa_traversal` (correctness only) | `QDFA.traverse`, `QDFA.traverse_iff` | `QDFA.lean` |
| Construction `𝒜'` | `FSA.quasiDet` | `QuasiDet.lean` |
| Lemma `quasidet_completion` | `FSA.reach_stabilizes` (via generic `reachR_succ_eq`, `reachR_stabilizes`) | `QuasiDet.lean`, `Reach.lean` |
| Lemmas `quasidet_inclusion_right/left` | `FSA.delta_quasiDet_reach`, `FSA.deltaStar_quasiDet` | `QuasiDet.lean` |
| Thm. quasi-determinization | `FSA.quasiDet_language`, `FSA.exists_quasiDet` (includes the `2^{|Q_i|+|X|}` state bound) | `QuasiDet.lean` |

### §3.2 Separators in Thompson automata

The Thompson construction is built structurally (`TState`, `thompson`), so that states of a
subexpression's automaton embed into the whole automaton. Algorithm `thompson_separator` is a
descent in the expression tree (`descend`). File: `Thompson.lean`.

| Thesis | Lean |
|---|---|
| Thompson construction, Types 1–5 | `thompson`, `tDelta`, `nstates`, `card_tState` |
| Inner states of a subautomaton only have transitions within it | `Pos.local` |
| Props. `thompson_sep_3`, `thompson_sep_6`: `X` separates the blocks | `thompson_isSeparator` |
| Prop. `thompson_sep_4`: `\|X\| = 2` | `ncard_thompsonSep_sepX` |
| Loop condition and Prop. `thompson_sep_5`: blocks of size `≤ 2\|Q\|/3` | `descend_bounds`, `ncard_block_zero/one` |
| Prop. `thompson_sep_2`: at most `\|Q\|` iterations | `descendSteps_le` |
| Thm. `thompson_separator` | `thompson_separator` |
| Quasi-determinization in `O(\|Σ\|·\|Q\|·2^{2\|Q\|/3})` with the state-balanced separator | `thompson_quasiDet` |
| Symbol occurrences `m`, targets of symbol transitions, `\|Q^Σ\| ≤ m + 1` (Prop. `thompson_essential`) | `nsym`, `symTargets`, `ncard_symTargets`, `essential_thompson` |
| Essential states of the two blocks | `ncard_essential_block_zero_le`, `ncard_essential_block_one_le` |
| Symbol-balanced variant of Alg. `thompson_separator` | `descendSym`, `descendSym_bounds`, `thompsonSepSym` |
| Thm. `thompson_separator_symbols`: blocks with `≤ 2m/3 + 1` essential states | `thompson_separator_symbols` |
| Cor. `quasidet_regex`: quasi-determinization in `O(\|Σ\|·\|Q\|·2^{2m/3})` | `thompson_quasiDet_symbols` |

### Chapter 4 (transducers)

| Thesis | Lean | File |
|---|---|---|
| Longest common prefix `⋀`, sequential distance, bounded variation | `lcp`, `prefix_lcp_iff`, `IsLcp`/`setLcp`, `dist`, `BoundedVariation` | `Lcp.lean` |
| FST, `Δ*`, prop. path ⇔ `Δ*` | `FST`, `FST.Star`, `FST.star_iff_exists_path` | `FST.lean` |
| `𝓡_T`, functional, trimmed, `𝒢_T` | `FST.relation`, `IsFunctional`, `IsTrimmed`, `graphEdges` | `FST.lean` |
| Subsequential FST, `δ*`, `λ*`, prop. path ⇔ `δ*, λ*`, `𝓕_T` | `SST`, `SST.lamStar_append_singleton`, `SST.isPath_iff`, `SST.relation` | `SST.lean` |
| Separator in an FST; props. graph ⇒ FST separator, small `Δ`, runs cross `X` | `FST.IsSeparator`, `isSeparator_of_graph`, `small_delta`, `exists_sep_of_star` | `FST.lean` |
| `Δᵢ_ε`, `Δᵢ_{fε}` | `FST.compClose`, `FST.compStep` | `FST.lean` |
| QSFST, `δ`, `λ = ⋀λᵢ`, `λ*`, `𝓡_T` | `QSFST` (extends `QDFA`), `olam`, `lamStar`, `relation` | `QSFST.lean` |
| Prop. `λ(δ*(q,u),σ)⁻¹λ*(q,u)⁻¹v ≃ λ*(q,uσ)⁻¹v`; prop. path ⇔ `δ*, λ*` | `QSFST.lquot_lamStar`, `QSFST.isPath_iff` | `QSFST.lean` |
| Alg. `qsfst_traversal`, Alg. `lcp` (correctness only) | `QSFST.traverse_sound`, `traverse_complete`, `prefix_lcpK_iff` | `QSFST.lean` |
| Construction `𝒯'` (repaired, see below) | `FST.quasiSubseq` | `QuasiSubseq.lean` |
| Lemmas `quasisubseq_inclusion_right/left` | `FST.step_some`, `FST.deltaStar_quasiSubseq`, `FST.quasiSubseq_relation_subset` | `QuasiSubseq.lean` |
| Lemma `quasisubseq_completion` | `FST.pending_bounded`, `reachable_quasiSubseq_finite`, `quasisubseq_completion` | `QuasiSubseq.lean` |
| Thm. quasi-subsequentialization | `FST.quasiSubseq_relation`, `FST.exists_quasiSubseq` | `QuasiSubseq.lean` |

### Complexity bounds

Cost model, as in the thesis: table lookups, membership tests, symbol comparisons and
concatenations cost 1 step; set operations in Alg. `quasi_det_sfsa` cost `|Q|`. Each algorithm is
written as a function that returns its result together with its step count. Each is proved to
compute its specification and to satisfy the stated bound.

| Thesis | Lean | Result |
|---|---|---|
| Alg. `qdfsa_traversal`, `O(kn)` | `QDFA.traverseT_spec`, `traverseT_cost_le` | exactly `1 + 5kn + k` steps |
| Alg. `lcp`, `O(kn)` with `n = min |wᵢ|` | `lcpCols_eq_lcpK`, `lcp_algorithm_cost_le` | at most `(|p| + 2)k`, where `|p| ≤ n` is the result |
| Alg. `qsfst_traversal`, `O(k(n+m))` | `QSFST.traverseT_eq`, `traverseT_cost_le` | at most `12k(n+1) + k|v|` when it returns `v` |
| Alg. `quasi_det_sfsa`: loop iterations | `quasiDetIterations_eq_frontier`, `quasiDetIterations_eq_subset` | **equal** to the number of states of the subset-construction DFA |
| Alg. `quasi_det_sfsa`, `O(k|Σ||Q|2^{|X|}Σᵢ2^{|Q_i|})` | `thesis_iteration_bound_false`, `thesis_runtime_bound_false` | **false**; corrected: `quasiDetCost_le`, `O(k|Σ||Q|·D)` with `D ≤ 2^{|Q|}` |

Files: `Complexity/Traversal.lean` and `Complexity/QuasiDet.lean`.

### Per-component quasi-determinization (new; not in the original thesis)

The new construction explores each component on its own, closing over **all** separator
values `x ⊆ X`. This avoids the global-state blow-up of Alg. `quasi_det_sfsa`. It matches the
eager variant in `impl/eager_quasi_determinize.h`. File: `PerComponent.lean`; the write-up is
Alg. `quasi_det_sfsa_components` in §3.5.

| Statement | Lean |
|---|---|
| `U_i`: closure of `sⁱ` under `P ↦ η_i(τ_i(P, σ), x)` for all `σ` and `x ⊆ X`; `T_i`: results of `τ_i` on `U_i` | `FSA.compClosure`, `FSA.tauImage` |
| Reachable states have components in `U_i` | `FSA.deltaStar_mem_compClosure` |
| `𝒜''` (quasi-states `U_i ∪ T_i`, `τ_i` on `U_i`, `η_i` on `T_i`) behaves like `𝒜'` and recognizes `𝓛_A` | `FSA.perComponent_deltaStar`, `perComponent_language` |
| `|U_i|, |T_i|, |U_i ∪ T_i| ≤ 2^{|Q_i| + |X|}` | `FSA.ncard_quasiStates_le` |
| The worklist processes each element of `U_i` exactly once | `FSA.perComponent_iterations` |
| Cost `O((|Σ| + 2^{|X|})·|Q|·2^{|X|}·Σᵢ2^{|Q_i|})` | `FSA.perComponentCost_le` |
| `blowup k`: `|U_i ∪ T_i| ≤ 4`, while Alg. `quasi_det_sfsa` needs `≥ 2^k` iterations | `FSA.blowup_perComponent` |

### Essential states

File: `Essential.lean`.

| Thesis | Lean |
|---|---|
| Def. `essential_states`: `Q^Σ` | `FSA.essential` |
| Prop. `essential_closure` | `FSA.compClose_eq_essential` |
| Lemma `quasidet_essential`: quasi-states are `Δ̂ᵢ_ε(B ∪ E)`, `\|U_i ∪ T_i\| ≤ 2^{m_i + \|X\|}` | `FSA.compStates_subset_kernels`, `FSA.ncard_compStates_le_essential` |
| Thm. `quasidet_components_essential`: cost `O((\|Σ\| + 2^{\|X\|})·\|Q\|·2^{\|X\|}·Σᵢ2^{m_i})` | `FSA.perComponentCost_le_essential` |

Prop. `essential_dfa` (`D ≤ 2^{|Q^Σ|}`) is not formalized.


## Modelling choices

- `Σ_ε = Option α`, words are `List α`, partitions `{X, Q_1, …, Q_k}` are `part : Q → Option (Fin k)`.
- The theorems need only the separator condition, not the thesis' nonemptiness/`k > 1`
  requirements (those are recorded in `IsKSeparated`).
- QDFA components have total `τ_i` and `ρ_i`; the thesis' `X ⊆ Q_i` is dropped (unused).
- `𝒜'` is defined with total tables. The thesis' incremental tables `𝒜'^{(n)}` are their
  restriction to `R^{(n)}`; `reach_stabilizes` shows `R^{(n)}` stabilizes at the reachable set.
  Therefore the propositions that `τ_i^{(n)}, ρ_i^{(n)}, …` are functions with
  `dom(ρ_i) = rng(τ_i)` hold by construction and are not stated separately.

Chapter 4:

- QSFST: `τ_i` is total and `λ_i` returns `Option` (`none` = no transition). The global
  `λ(q,σ)` ignores undefined components; `λ*` is `none` once a step has no transition at all.
- `ψ_i` picks some final pair's pending output; on reachable states the choice doesn't
  matter, because the transducer is functional.
- Bounded variation is stated for the relation `𝓡_T`. For functional `T` this is the thesis'
  definition. Termination (`pending_bounded`) uses only trimmedness and bounded variation, not
  functionality.
- The output alphabet `Ω` is assumed finite for termination (`[Finite β]`), as in the thesis.

## Note on the thesis proof of `quasidet_inclusion_right`

The chain of equalities rewrites `Δ̂ʲ_ε(Δ̂_f(p^r, σ))` as `Δ̂ʲ_ε(Δ̂ʳ_ε(Δ̂_f(p^r, σ)) ∩ X)`. That
rewrite uses the last proposition of §3.1, which requires `Δ̂_f(p^r, σ) ⊆ 𝒞(Q_r)`. This fails
when `p^r` contains a separator state with a `σ`-transition into some other `Q_j`.
Counterexample: `X = {x}`, `Q_1 = {a}`, `Q_2 = {b}`, `x →σ b`, `p^1 = {x}`.

The theorem is still true, because the construction keeps `p^i ∩ X` the same for every `i`.
The Lean proof gets this from a stronger invariant (`deltaStar_quasiDet`):

    δ*(s, w)^i = {q | ∃ s ∈ S, ⟨s, w, q⟩ ∈ Δ*} ∩ 𝒞(Q_i)

so each quasi-state is exactly the projection of the subset-construction state onto its
component.

## Problem in §4.4: the construction of `𝒯'` is not well-defined

The thesis sets `τ_i(qⁱ, σ) = {⟨p, λ(q,σ)⁻¹w⟩ | ⟨p,w⟩ ∈ Δⁱ_{fε}(qⁱ, σ)}` with
`λ(q,σ) = ⋀ⱼ λⱼ(qʲ, σ)`. The value depends on all components of `q`, but `τ_i` is keyed by
`qⁱ` alone. So the proposition "`τ_i^{(n)}` are functions" is false.

Counterexample (trimmed, functional, finite domain, `k = 2`, `X = {x}`):

- `S = {a0, b0, x}`, `F = {af, bf, x}`.
- `Q₁`: `a0 -c/ε→ a1`, `a0 -d/ε→ a1`, `a1 -σ/z→ a2`, `a2 -e/y→ af`.
- `Q₂`: `b0 -c/ε→ b1 -σ/ε→ b3 -e/zy→ bf`, and `b0 -d/ε→ b2 -σ/zy→ b4 -e/ε→ bf`.
- The relation is `{ε ↦ ε, cσe ↦ zy, dσe ↦ zy}`.

After `c` and after `d`, the first component is `{⟨a1, ε⟩}` in both cases. On `σ`:

- After `c`: `λ = z ∧ ε = ε`, so `τ₁ = {⟨a2, z⟩}`.
- After `d`: `λ = z ∧ zy = z`, so `τ₁ = {⟨a2, ε⟩}`.

**Repair.** The formalization keeps the thesis' QSFST definition and changes only the
construction (`FST.quasiSubseq`):

- `τ_i` doesn't normalize.
- A separator state is a pair `⟨ℓ, E⟩`, so the global lcp `λ(q,σ)` flows through the separator
  channel (`η_x` takes lcps and unions).
- `η_i(T, ⟨m, E⟩) = {⟨p, m⁻¹w⟩ | ⟨p,w⟩ ∈ T ∪ Δ̂ⁱ_ε(E)}` does the normalization.

As in Chapter 3, the proof rests on an exact invariant (`deltaStar_quasiSubseq`). It also
covers the separator-sharing gap described above for `quasidet_inclusion_right`, which recurs
in `quasisubseq_inclusion_right`.

Minor issues noticed along the way:

- The proof of `quasisubseq_inclusion_right` stops after the inductive step, without the final
  `ψ` argument.
- In `quasisubseq_completion`, the pair `⟨p'', u''⟩` with `u' ∧ u'' = ε` may lie in a different
  component than `⟨p', u'⟩`. The argument also needs `w ≠ ε`, because the start state is not
  normalized.
- `τ_i^{(n+1)}` refers to `λ^{(n)}(q,σ)`, but `λ^{(n)}` does not yet contain `(q,σ)` for
  `q ∈ R_n`.
- Alg. `qsfst_traversal`, line 8, reads `λ_j(q_j, σ_j)`; it should be `σ_i`.

## Problem in §3.5: the runtime bound for Alg. `quasi_det_sfsa` is false

The thesis bounds the number of while-loop iterations by `2^{|X|}(1 + Σᵢ 2^{|Q_i|})`. That
counts entries of the per-component tables. The loop, however, iterates over *global* states:
tuples of quasi-states, one per state in `R`. By the invariant `deltaStar_quasiDet`, global
states correspond one-to-one to the states of the subset-construction DFA
(`quasiDetIterations_eq_subset`). The number of those can be close to `∏ᵢ 2^{|Q_i|}`, not `Σᵢ`.

Counterexample `blowup k`, with alphabet `Fin k`:

- Start state `x` (the separator), with `ε`-transitions to `q_1, …, q_k`.
- `q_j` loops on every letter except `j`.
- So `|X| = |Q_i| = 1` and `|Σ| = k`.

After reading `w`, exactly the `q_j` with `j ∉ w` are alive, so the loop runs at least `2^k`
times (`blowup_iterations`). The thesis' iteration bound is `4k + 2`, which fails for `k ≥ 5`.
Its runtime bound is `4k³(k+1)`, which fails for every constant factor.

The space claim (table sizes `Σᵢ 2^{|Q_i|+|X|}`) is unaffected. Only the time to build the
tables is underestimated: it is `O(k|Σ||Q|·D)`, where `D` is the size of the DFA that the
construction is meant to avoid building.

Smaller issues in the complexity proofs:

- Alg. `lcp` costs `Θ(k)` even when the shortest word is empty, so its bound is `O(k(n+1))`
  rather than `O(kn)`.
- The `O(k(n+m))` bound for `qsfst_traversal` needs early exit in Alg. `lcp`. The per-call bound
  `O(k·min|lⱼ|)` stated in the thesis does not sum to `O(km)`, because `min|lⱼ|` can be much
  larger than the common prefix that ends up in the output.
- `prop:quasidet_auto_1` is referenced but never defined, and `Visited_x`, `Visited_i` don't
  occur in Alg. `quasi_det_sfsa`.

## Not yet formalized

- Imperative correctness of Alg. `quasi_det_sfsa`. Its iteration count is taken from the
  frontier sequence `R^{(n)}`, as justified by the thesis' proposition `𝒜_c = 𝒜'`. The
  algorithms are modelled as functional programs with explicit step counts, not run on an
  operational machine model.
- Prop. `essential_dfa`: the subset construction has at most `2^{|Q^Σ|}` reachable states.
- §3.2: the planarity of the graphs of Thompson automata (Mathlib has no theory of planar
  embeddings; the result only motivates the use of separators), and the correctness of the
  Thompson construction itself (cited in the thesis).
- Cited results: the trimming algorithm (Mihov–Schulz) and Mohri's subsequentialization theorem.
- For transducers, the finite-state device is the restriction of `𝒯'` to its finitely many
  reachable states. It is not built as a separate structure with finite component types.
