#ifndef SQDFA_EPSILON_H_
#define SQDFA_EPSILON_H_

#include <queue>

#include "nfa.h"
#include "transitions.h"
#include "types.h"

namespace sqdfa {

struct PendingTransition {
  uint32_t from_idx;
  char value;
  uint32_t to_idx;
};

void ComputeEpsilonClosure(Nfa* nfa) {
  std::queue<PendingTransition> pending_transitions;
  for (uint32_t from = 0; from < nfa->StatesCount(); from++) {
    uint32_t transition_idx = nfa->state_transitions_[from];
    while (transition_idx != uint32_null) {
      const Transition<char>& transition = nfa->transitions_[transition_idx];
      if (transition.value == char_empty) {
        pending_transitions.push(
            PendingTransition{from, transition.value, transition.target});
      }
      transition_idx = transition.next;
    }
  }

  while (!pending_transitions.empty()) {
    auto pending_transition = pending_transitions.front();
    pending_transitions.pop();

    if (pending_transition.from_idx == pending_transition.to_idx) {
      return;
    }
  }
}

}  // namespace sqdfa

#endif  // SQDFA_EPSILON_H_
