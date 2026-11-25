# Separators for Quasi-Determinization of Finite-State Devices

[![Sqdfsa](https://github.com/sgatev/sqdfsa-old/actions/workflows/sqdfsa.yml/badge.svg?branch=main)](https://github.com/sgatev/sqdfsa-old/actions/workflows/sqdfsa.yml)

**[Download the latest thesis PDF](https://github.com/sgatev/sqdfsa-old/releases/download/thesis-latest/thesis.pdf)**
(rebuilt by CI on every push to `main`)

Determinizing a finite-state automaton can blow up the number of states exponentially. The
thesis studies automata whose graphs contain a separator: a set of states `X` whose removal
splits the rest into components `Q_1, …, Q_k` with no transitions between them. For such
automata, a *quasi-deterministic* automaton keeps one deterministic quasi-state per component
and synchronizes the components through the separator. It processes a word in `O(k)` time per
symbol and needs at most `2^{m_i + |X_i|}` quasi-states in its `i`-th component, where `m_i`
counts the essential states of `Q_i` and `X_i` is its boundary. The same approach applies to
functional finite-state transducers of bounded variation.

## Repository

| Directory | Contents |
|---|---|
| [`thesis/`](thesis) | LaTeX sources of the thesis. Build with `thesis/build.sh` (needs `latexmk` and XeLaTeX). |
| [`lean/`](lean) | Lean 4 + Mathlib formalization of the main results, with a map from the thesis to the Lean names. See [`lean/README.md`](lean/README.md). |
| [`impl/`](impl) | C++20 implementation of the constructions for automata, with tests and benchmarks. See [`impl/README.md`](impl/README.md). |

```sh
(cd impl && bazel test -c opt --config=opt //...)   # implementation tests
(cd lean && lake exe cache get && lake build)        # formalization
./thesis/build.sh                                    # thesis PDF
```
