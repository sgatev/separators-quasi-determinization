#ifndef SQDFA_NFA_H_
#define SQDFA_NFA_H_

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <string_view>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "bit_set.h"
#include "overload.h"
#include "pool.h"
#include "transitions.h"
#include "types.h"

namespace sqdfa {

class Nfa {
 public:
  uint32_t AddState() noexcept;

  void AddTransition(uint32_t from, char symbol, uint32_t to) noexcept;

  bool Match(const std::string_view input) const noexcept;

  template <class Container>
  void MakeTransitions(const Container& states, char symbol,
                       std::vector<uint32_t>* next_states) const noexcept {
    BitSet bits(state_transitions_.size());
    for (uint32_t state : states) {
      uint32_t tidx = state_transitions_[state];
      while (tidx != uint32_null) {
        if (transitions_[tidx].value == symbol &&
            !bits.Test(transitions_[tidx].target)) {
          next_states->push_back(transitions_[tidx].target);
          bits.Set(transitions_[tidx].target);
        }
        tidx = transitions_[tidx].next;
      }
    }
    int i = 0;
    while (true) {
      const uint32_t size = next_states->size();
      for (; i < size; i++) {
        uint32_t tidx = state_transitions_[(*next_states)[i]];
        while (tidx != uint32_null) {
          if (transitions_[tidx].value == char_empty &&
              !bits.Test(transitions_[tidx].target)) {
            next_states->push_back(transitions_[tidx].target);
            bits.Set(transitions_[tidx].target);
          }
          tidx = transitions_[tidx].next;
        }
      }
      if (size == next_states->size()) {
        break;
      }
    }
    uint32_t idx = 0;
    for (uint32_t state = 0; state < state_transitions_.size(); state++) {
      if (bits.Test(state)) {
        (*next_states)[idx++] = state;
      }
    }
  }

  void EpsilonClosure(std::vector<uint32_t>* states) const noexcept;

  uint32_t StatesCount() const noexcept;

  uint32_t TransitionsCount() const noexcept;

  absl::flat_hash_set<char> alphabet;
  uint32_t start_state;
  uint32_t final_state;

  std::vector<uint32_t> state_transitions_;
  std::vector<Transition<char>> transitions_;
};

}  // namespace sqdfa

#endif  // SQDFA_NFA_H_
