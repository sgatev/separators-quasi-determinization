# Implementation

C++20 implementation of the constructions in the thesis: Thompson automata, separators,
the subset construction, Algorithm `quasi_det_sfsa` (`quasi_determinize.h`) and the
per-component construction (`eager_quasi_determinize.h`, Algorithm
`quasi_det_sfsa_components`).

Imported from the original `qdfa` repository (2019–2020) without its history.

```sh
bazel test -c opt --config=opt //...   # unit tests
bazel run -c opt --config=opt //:main   # benchmark on the thesis' expressions
```

Requires Bazel 7 or later (Bzlmod); dependencies come from the Bazel Central Registry.

## Changes since the import

- Fixed undefined behaviour in both quasi-determinization algorithms: since a refactoring in
  January 2020, `absl::c_set_union`/`c_set_intersection` wrote through `begin()` of empty
  vectors, which crashed at the first call. They now write through `std::back_inserter`.
- Migrated the build from `WORKSPACE` to `MODULE.bazel`, which Bazel 9 requires, and
  loaded the C++ rules from `rules_cc`. `-Wall -Werror` now apply only to this
  project's sources.
- Fixed a missing `#include <stack>` and a `-Wrange-loop-construct` warning.
- Updated the tests to the current API. They now check that the DFA and both QDFA
  constructions (with 2 and 3 components) agree with the NFA on all words up to length 10.
- `main` runs the expressions of the thesis' comparison tables, including the larger
  `(0|1)*.0.(0|1)^20`, and prints the number of main-loop iterations of both algorithms.
- Both algorithms skip quasi-states that were already processed. Previously a state pushed
  twice before being processed was processed twice; the resulting tables were the same.
- The per-component algorithm computes the `eta` entries once per distinct result of `tau`,
  instead of once per (quasi-state, symbol) pair. The constructed device is unchanged.
