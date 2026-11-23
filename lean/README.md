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
| Lemma `quasidet_completion` | `FSA.R`, `FSA.R_succ_eq`, `FSA.reach_stabilizes` | `QuasiDet.lean` |
| Lemmas `quasidet_inclusion_right/left` | `FSA.delta_quasiDet_reach`, `FSA.deltaStar_quasiDet` | `QuasiDet.lean` |
| Thm. quasi-determinization | `FSA.quasiDet_language`, `FSA.exists_quasiDet` (includes the `2^{|Q_i|+|X|}` state bound) | `QuasiDet.lean` |

## Modelling choices

- `Σ_ε = Option α`, words are `List α`, partitions `{X, Q_1, …, Q_k}` are `part : Q → Option (Fin k)`.
- The theorems need only the separator condition, not the thesis' nonemptiness/`k > 1`
  requirements (those are recorded in `IsKSeparated`).
- QDFA components have total `τ_i` and `ρ_i`; the thesis' `X ⊆ Q_i` is dropped (unused).
- `𝒜'` is defined with total tables. The thesis' incremental tables `𝒜'^{(n)}` are their
  restriction to `R^{(n)}`; `reach_stabilizes` shows `R^{(n)}` stabilizes at the reachable set.
  Therefore the propositions that `τ_i^{(n)}, ρ_i^{(n)}, …` are functions with
  `dom(ρ_i) = rng(τ_i)` hold by construction and are not stated separately.

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

## Not yet formalized

- Complexity bounds: `O(kn)` traversal, `O(k|Σ||Q|2^{|X|}Σ2^{|Q_i|})` for Alg. `quasi_det_sfsa`,
  and the imperative correctness of Alg. `quasi_det_sfsa`.
- §3.2: Thompson automata and their constant-size separators.
- Chapter 4: separated transducers and quasi-subsequentialization.
