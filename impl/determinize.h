#ifndef SQDFA_DETERMINIZE_H_
#define SQDFA_DETERMINIZE_H_

#include "dfa.h"
#include "nfa.h"

#include "absl/base/attributes.h"

namespace sqdfa {

// Constructs a deterministic finite-state automaton from a finite-state
// automaton.
ABSL_MUST_USE_RESULT Dfa Determinize(const Nfa &nfa);

}  // namespace sqdfa

#endif  // SQDFA_DETERMINIZE_H_
