#ifndef SQDFA_SEPARATOR_H_
#define SQDFA_SEPARATOR_H_

#include <algorithm>
#include <array>
#include <cinttypes>
#include <iterator>
#include <stack>
#include <vector>

#include "absl/base/attributes.h"
#include "nfa.h"
#include "thompson_description.h"
#include "types.h"

namespace sqdfa {

template <int K>
struct SeparatedStates {
  std::vector<uint32_t> separator;
  std::array<std::vector<uint32_t>, K> components;
};

ABSL_MUST_USE_RESULT uint32_t FindInternal(ThompsonDescription& description,
                                           uint32_t node_idx,
                                           SeparatorWeight weight);

void Insert(const ThompsonDescription& description, const ThompsonNode& node,
            std::unordered_set<uint32_t>* outside_states);

// The essential states of a Thompson automaton: its start state and the
// targets of transitions labelled with symbols of the alphabet. Every
// quasi-state of component i is determined by its essential states in Q_i
// and its separator states.
ABSL_MUST_USE_RESULT std::vector<uint32_t> EssentialStates(
    const ThompsonDescription& description);

template <int K>
ABSL_MUST_USE_RESULT SeparatedStates<K> SeparateStates(
    ThompsonDescription description,
    SeparatorWeight weight = SeparatorWeight::kSymbols) {
  std::unordered_set<uint32_t> separator;
  std::unordered_set<uint32_t> nodes;
  nodes.insert(description.NodeIdx());

  for (int i = 1; i < K; i++) {
    uint32_t node_idx =
        *std::max_element(std::begin(nodes), std::end(nodes),
                          [&](uint32_t first, uint32_t second) {
                            const ThompsonNode& a = description.Node(first);
                            const ThompsonNode& b = description.Node(second);
                            return weight == SeparatorWeight::kStates
                                       ? a.states_count < b.states_count
                                       : a.symbols_count < b.symbols_count;
                          });

    const uint32_t inside_data_idx =
        FindInternal(description, node_idx, weight);
    separator.insert(description.Node(inside_data_idx).start_state);
    separator.insert(description.Node(inside_data_idx).final_state);

    nodes.insert(inside_data_idx);
    nodes.insert(description.NodeIdx());
  }

  SeparatedStates<K> state_separation;
  state_separation.separator.insert(std::end(state_separation.separator),
                                    std::begin(separator), std::end(separator));
  std::sort(std::begin(state_separation.separator),
            std::end(state_separation.separator));

  int j = 0;
  for (uint32_t node_idx : nodes) {
    std::unordered_set<uint32_t> states;
    Insert(description, description.Node(node_idx), &states);
    state_separation.components[j].insert(
        std::end(state_separation.components[j]), std::begin(states),
        std::end(states));
    std::sort(std::begin(state_separation.components[j]),
              std::end(state_separation.components[j]));

    j++;
  }

  return state_separation;
}

}  // namespace sqdfa

#endif  // SQDFA_SEPARATOR_H_
