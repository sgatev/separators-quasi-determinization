#include "nfa.h"

#include <string_view>
#include <vector>

#include "bit_set.h"
#include "types.h"

namespace sqdfa {

uint32_t Nfa::AddState() noexcept {
  const uint32_t state = state_transitions_.size();
  state_transitions_.push_back(uint32_null);
  return state;
}

void Nfa::AddTransition(uint32_t from, char symbol, uint32_t to) noexcept {
  if (symbol == '~') {
    symbol = char_empty;
  }
  transitions_.emplace_back(state_transitions_[from], to, symbol);
  state_transitions_[from] = transitions_.size() - 1;
  if (symbol != char_empty) {
    alphabet.insert(symbol);
  }
}

bool Nfa::Match(const std::string_view input) const noexcept {
  absl::flat_hash_set<uint32_t> active_states;
  active_states.insert(start_state);

  while (true) {
    absl::flat_hash_set<uint32_t> next_active_states = active_states;
    for (uint32_t state : active_states) {
      uint32_t tidx = state_transitions_[state];
      while (tidx != uint32_null) {
        if (transitions_[tidx].value == char_empty) {
          next_active_states.insert(transitions_[tidx].target);
        }
        tidx = transitions_[tidx].next;
      }
    }
    if (next_active_states.size() == active_states.size()) {
      break;
    }
    active_states = next_active_states;
  }

  for (char symbol : input) {
    absl::flat_hash_set<uint32_t> next_active_states;
    for (uint32_t state : active_states) {
      uint32_t tidx = state_transitions_[state];
      while (tidx != uint32_null) {
        if (transitions_[tidx].value == symbol) {
          next_active_states.insert(transitions_[tidx].target);
        }
        tidx = transitions_[tidx].next;
      }
    }
    active_states = next_active_states;

    while (true) {
      absl::flat_hash_set<uint32_t> next_active_states = active_states;
      for (uint32_t state : active_states) {
        uint32_t tidx = state_transitions_[state];
        while (tidx != uint32_null) {
          if (transitions_[tidx].value == char_empty) {
            next_active_states.insert(transitions_[tidx].target);
          }
          tidx = transitions_[tidx].next;
        }
      }
      if (next_active_states.size() == active_states.size()) {
        break;
      }
      active_states = next_active_states;
    }
  }

  return active_states.find(final_state) != active_states.end();
}

void Nfa::EpsilonClosure(std::vector<uint32_t>* states) const noexcept {
  BitSet bits(state_transitions_.size());
  for (uint32_t state : *states) {
    bits.Set(state);
  }
  int i = 0;
  while (true) {
    const uint32_t size = states->size();
    for (; i < size; i++) {
      uint32_t tidx = state_transitions_[(*states)[i]];
      while (tidx != uint32_null) {
        if (transitions_[tidx].value == char_empty &&
            !bits.Test(transitions_[tidx].target)) {
          states->push_back(transitions_[tidx].target);
          bits.Set(transitions_[tidx].target);
        }
        tidx = transitions_[tidx].next;
      }
    }
    if (size == states->size()) {
      break;
    }
  }
  uint32_t idx = 0;
  for (uint32_t state = 0; state < state_transitions_.size(); state++) {
    if (bits.Test(state)) {
      (*states)[idx++] = state;
    }
  }
}

uint32_t Nfa::StatesCount() const noexcept { return state_transitions_.size(); }

uint32_t Nfa::TransitionsCount() const noexcept { return transitions_.size(); }

}  // namespace sqdfa
