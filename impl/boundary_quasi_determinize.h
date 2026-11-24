#ifndef SQDFA_BOUNDARY_QUASI_DETERMINIZE_H_
#define SQDFA_BOUNDARY_QUASI_DETERMINIZE_H_

#include <algorithm>
#include <array>
#include <cassert>
#include <cinttypes>
#include <iterator>
#include <stack>
#include <string_view>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/base/attributes.h"
#include "absl/container/flat_hash_map.h"
#include "composite_state.h"
#include "nfa.h"
#include "separator.h"

namespace sqdfa {

// The boundaries X_1, ..., X_K of a separation: X_i contains the separator
// states that share a transition with a state of Q_i. Separator states that
// share no transition with any Q_i are added to X_1, so that the boundaries
// cover X.
template <int K>
ABSL_MUST_USE_RESULT std::array<std::vector<uint32_t>, K> ComputeBoundaries(
    const Nfa& nfa, const SeparatedStates<K>& separated_states) {
  constexpr uint32_t kSeparator = uint32_null;
  std::vector<uint32_t> component_of(nfa.StatesCount(), kSeparator);
  for (int i = 0; i < K; i++) {
    for (uint32_t state : separated_states.components[i]) {
      if (!std::binary_search(std::begin(separated_states.separator),
                              std::end(separated_states.separator), state)) {
        component_of[state] = i;
      }
    }
  }

  std::array<std::vector<uint32_t>, K> boundaries;
  std::vector<bool> covered(nfa.StatesCount(), false);
  auto add = [&](uint32_t component, uint32_t separator_state) {
    boundaries[component].push_back(separator_state);
    covered[separator_state] = true;
  };
  for (uint32_t from = 0; from < nfa.StatesCount(); from++) {
    for (uint32_t tidx = nfa.state_transitions_[from]; tidx != uint32_null;
         tidx = nfa.transitions_[tidx].next) {
      const uint32_t to = nfa.transitions_[tidx].target;
      if (component_of[from] != kSeparator && component_of[to] == kSeparator) {
        add(component_of[from], to);
      }
      if (component_of[to] != kSeparator && component_of[from] == kSeparator) {
        add(component_of[to], from);
      }
    }
  }
  for (uint32_t state : separated_states.separator) {
    if (!covered[state]) {
      add(0, state);
    }
  }
  for (std::vector<uint32_t>& boundary : boundaries) {
    std::sort(std::begin(boundary), std::end(boundary));
    boundary.erase(std::unique(std::begin(boundary), std::end(boundary)),
                   std::end(boundary));
  }
  return boundaries;
}

// A quasi-deterministic finite-state automaton whose components are indexed
// by their boundaries. Separator states are bit masks over X. The i-th
// component reads only the bits of X_i of the separator state.
template <int K>
class BoundaryQdfa {
 public:
  struct TauEntry {
    // The row of the eta table of tau(P, sigma) restricted to Q_i u X_i.
    uint32_t row;
    // rho(tau(P, sigma)): the separator states reached, as a mask over X.
    uint64_t rho;
  };

  struct Component {
    // Bit positions in X of the states of X_i.
    std::vector<int> boundary_bits;
    uint32_t start_state;
    // tau[state * alphabet_size + symbol_index].
    std::vector<TauEntry> tau;
    std::vector<bool> final_states;
    // eta[row << |X_i| | compressed mask].
    std::vector<uint32_t> eta;
    // Number of distinct quasi-states (explored states and tau results).
    uint32_t quasi_states_count = 0;
    // Number of entries of tau with nonempty values.
    uint32_t nonempty_tau_count = 0;

    uint32_t Compress(uint64_t mask) const {
      uint32_t result = 0;
      for (size_t b = 0; b < boundary_bits.size(); b++) {
        result |= static_cast<uint32_t>((mask >> boundary_bits[b]) & 1) << b;
      }
      return result;
    }
  };

  bool Match(const std::string_view input) const {
    std::array<uint32_t, K> state;
    for (int i = 0; i < K; i++) {
      state[i] = components_[i].start_state;
    }
    for (char symbol : input) {
      const int symbol_index = symbol_index_[static_cast<unsigned char>(symbol)];
      if (symbol_index < 0) {
        return false;
      }
      std::array<TauEntry, K> tau;
      uint64_t separator = 0;
      for (int i = 0; i < K; i++) {
        tau[i] = components_[i].tau[state[i] * alphabet_size_ + symbol_index];
        separator |= tau[i].rho;
      }
      for (int i = 0; i < K; i++) {
        const Component& component = components_[i];
        state[i] = component.eta[(static_cast<size_t>(tau[i].row)
                                  << component.boundary_bits.size()) |
                                 component.Compress(separator)];
      }
    }
    for (int i = 0; i < K; i++) {
      if (components_[i].final_states[state[i]]) {
        return true;
      }
    }
    return false;
  }

  uint32_t StatesCount() const {
    uint32_t result = 0;
    for (const Component& component : components_) {
      result += component.quasi_states_count;
    }
    return result;
  }

  // Entries of tau with nonempty values plus entries of eta, as for Qdfa.
  uint32_t TransitionsCount() const {
    uint32_t result = 0;
    for (const Component& component : components_) {
      result += component.nonempty_tau_count + component.eta.size();
    }
    return result;
  }

  std::array<Component, K> components_;
  std::array<int, 256> symbol_index_;
  uint32_t alphabet_size_ = 0;
};

// Per-component quasi-determinization with boundaries: the quasi-states of
// component i are subsets of Q_i u X_i, and eta_i is tabulated for the 2^|X_i|
// subsets of X_i only. Counts the explored quasi-states in iterations.
template <int K>
ABSL_MUST_USE_RESULT BoundaryQdfa<K> BoundaryQuasiDeterminize(
    const Nfa& nfa, const SeparatedStates<K>& separated_states,
    uint64_t* iterations = nullptr) {
  const std::vector<uint32_t>& separator = separated_states.separator;
  assert(separator.size() <= 64);
  const std::array<std::vector<uint32_t>, K> boundaries =
      ComputeBoundaries<K>(nfa, separated_states);

  BoundaryQdfa<K> qdfa;
  std::vector<char> alphabet(std::begin(nfa.alphabet), std::end(nfa.alphabet));
  std::sort(std::begin(alphabet), std::end(alphabet));
  qdfa.alphabet_size_ = alphabet.size();
  qdfa.symbol_index_.fill(-1);
  for (size_t s = 0; s < alphabet.size(); s++) {
    qdfa.symbol_index_[static_cast<unsigned char>(alphabet[s])] = s;
  }

  auto separator_bit = [&](uint32_t state) {
    return std::lower_bound(std::begin(separator), std::end(separator),
                            state) -
           std::begin(separator);
  };
  auto separator_mask = [&](const std::vector<uint32_t>& states) {
    uint64_t mask = 0;
    for (uint32_t state : states) {
      if (std::binary_search(std::begin(separator), std::end(separator),
                             state)) {
        mask |= uint64_t{1} << separator_bit(state);
      }
    }
    return mask;
  };

  std::vector<uint32_t> start_closure = {nfa.start_state};
  nfa.EpsilonClosure(&start_closure);
  std::sort(std::begin(start_closure), std::end(start_closure));

  for (int i = 0; i < K; i++) {
    typename BoundaryQdfa<K>::Component& component = qdfa.components_[i];
    const std::vector<uint32_t>& boundary = boundaries[i];
    for (uint32_t state : boundary) {
      component.boundary_bits.push_back(separator_bit(state));
    }

    // Q_i u X_i.
    std::vector<uint32_t> part;
    for (uint32_t state : separated_states.components[i]) {
      if (!std::binary_search(std::begin(separator), std::end(separator),
                              state)) {
        part.push_back(state);
      }
    }
    part.insert(std::end(part), std::begin(boundary), std::end(boundary));
    std::sort(std::begin(part), std::end(part));
    auto restrict = [&](const std::vector<uint32_t>& states) {
      std::vector<uint32_t> result;
      absl::c_set_intersection(states, part, std::back_inserter(result));
      return CompositeState(result);
    };

    // The closures Delta_eps(E) n (Q_i u X_i) for E a subset of X_i.
    const uint32_t subsets = uint32_t{1} << boundary.size();
    std::vector<std::vector<uint32_t>> boundary_closures(subsets);
    for (uint32_t e = 0; e < subsets; e++) {
      std::vector<uint32_t> states;
      for (size_t b = 0; b < boundary.size(); b++) {
        if (e >> b & 1) {
          states.push_back(boundary[b]);
        }
      }
      nfa.EpsilonClosure(&states);
      std::sort(std::begin(states), std::end(states));
      CompositeState restricted = restrict(states);
      boundary_closures[e].assign(std::begin(restricted), std::end(restricted));
    }

    // Ids of the explored quasi-states (U_i), and of the distinct values of
    // tau restricted to Q_i u X_i (the rows of eta).
    absl::flat_hash_map<CompositeState, uint32_t> explored;
    absl::flat_hash_map<CompositeState, uint32_t> rows;
    absl::flat_hash_map<CompositeState, bool> quasi_states;
    std::vector<CompositeState> pending;

    auto explore = [&](const CompositeState& state) {
      quasi_states[state] = true;
      auto [it, inserted] = explored.try_emplace(state, explored.size());
      if (inserted) {
        pending.push_back(state);
      }
      return it->second;
    };

    component.start_state = explore(restrict(start_closure));
    // States are explored in order of their ids, so that tau and final_states
    // can be indexed by them.
    for (size_t next = 0; next < pending.size(); next++) {
      const CompositeState state = pending[next];
      if (iterations != nullptr) {
        ++*iterations;
      }
      component.final_states.push_back(std::binary_search(
          std::begin(state), std::end(state), nfa.final_state));

      for (char symbol : alphabet) {
        std::vector<uint32_t> next_states;
        nfa.MakeTransitions(state, symbol, &next_states);
        const CompositeState tau = restrict(next_states);
        if (!tau.empty()) {
          component.nonempty_tau_count++;
        }
        quasi_states[tau] = true;

        auto [row_it, new_row] = rows.try_emplace(tau, rows.size());
        if (new_row) {
          component.eta.resize(component.eta.size() + subsets);
          for (uint32_t e = 0; e < subsets; e++) {
            std::vector<uint32_t> eta;
            absl::c_set_union(tau, boundary_closures[e],
                              std::back_inserter(eta));
            // explore may reallocate pending but not eta.
            const uint32_t eta_id = explore(CompositeState(eta));
            component.eta[(static_cast<size_t>(row_it->second)
                           << boundary.size()) |
                          e] = eta_id;
          }
        }
        component.tau.push_back(
            {row_it->second, separator_mask(next_states)});
      }
    }
    component.quasi_states_count = quasi_states.size();
  }
  return qdfa;
}

}  // namespace sqdfa

#endif  // SQDFA_BOUNDARY_QUASI_DETERMINIZE_H_
