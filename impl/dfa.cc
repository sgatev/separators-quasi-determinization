#include "dfa.h"

#include "types.h"

namespace sqdfa {

bool Dfa::Match(const std::string_view input) const {
  uint32_t state = start_state_;
  for (const char symbol : input) {
    state =
        FindTransitionTarget(transitions_, state_transitions_[state], symbol);
    if (state == uint32_null) {
      return false;
    }
  }
  return final_states_[state];
}

uint32_t Dfa::AddState() {
  const uint32_t state = state_transitions_.size();
  state_transitions_.push_back(uint32_null);
  final_states_.push_back(false);
  return state;
}

void Dfa::AddTransition(uint32_t from, char symbol, uint32_t to) {
  if (FindTransitionTarget(transitions_, state_transitions_[from], symbol) !=
      uint32_null) {
    return;
  }
  transitions_.emplace_back(state_transitions_[from], to, symbol);
  state_transitions_[from] = transitions_.size() - 1;
}

void Dfa::SetStartState(uint32_t state) { start_state_ = state; }

void Dfa::MakeFinalState(uint32_t state) { final_states_[state] = true; }

uint32_t Dfa::StatesCount() const { return state_transitions_.size(); }

uint32_t Dfa::TransitionsCount() const { return transitions_.size(); }

}  // namespace sqdfa
