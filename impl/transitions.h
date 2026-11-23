#ifndef SQDFA_TRANSITIONS_H_
#define SQDFA_TRANSITIONS_H_

#include <cinttypes>

#include "absl/base/attributes.h"
#include "types.h"

namespace sqdfa {

// Automaton transition.
template <typename Value>
struct Transition {
  Transition(uint32_t next, uint32_t target, Value value) noexcept
      : next(next), target(target), value(value) {}

  // Index of the next transition going out of the same state.
  const uint32_t next;

  // State reached by the transition.
  const uint32_t target;

  // Value that triggers the transition.
  const Value value;
};

// Returns the state reached by a transition or null if such is not present.
template <typename Transitions, typename Value>
ABSL_MUST_USE_RESULT uint32_t FindTransitionTarget(
    const Transitions &transitions, uint32_t idx, const Value value) noexcept {
  while (idx != uint32_null) {
    if (transitions[idx].value == value) {
      return transitions[idx].target;
    }
    idx = transitions[idx].next;
  }
  return uint32_null;
}

}  // namespace sqdfa

#endif  // SQDFA_TRANSITIONS_H_
