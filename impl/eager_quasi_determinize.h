#ifndef SQDFA_EAGER_QUASI_DETERMINIZE_H_
#define SQDFA_EAGER_QUASI_DETERMINIZE_H_

#include <algorithm>
#include <array>
#include <cinttypes>
#include <iterator>
#include <stack>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/base/attributes.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "composite_state.h"
#include "nfa.h"
#include "pool.h"
#include "qdfa.h"
#include "separator.h"

namespace sqdfa {

template <int K>
ABSL_MUST_USE_RESULT Qdfa<K> EagerQuasiDeterminize(
    const Nfa &nfa, const SeparatedStates<K> &separated_states,
    uint64_t *iterations = nullptr) {
  std::array<std::vector<uint32_t>, K> parts;
  for (int i = 0; i < K; i++) {
    absl::c_set_union(separated_states.components[i],
                      separated_states.separator, std::back_inserter(parts[i]));
  }

  std::array<absl::flat_hash_map<CompositeState, uint32_t>, K> composite_states;
  absl::flat_hash_map<CompositeState, uint32_t> composite_separator_states;
  Pool<std::vector<uint32_t>> nfa_states_pool(
      [](std::vector<uint32_t> *states) { states->clear(); });
  absl::flat_hash_set<std::pair<CompositeState, int>> visited;
  // Results of tau whose eta transitions have already been added.
  absl::flat_hash_set<std::pair<CompositeState, int>> extended;

  Qdfa<K> qdfa;

  // Initialize all separator supersets.
  for (int i = 0; i <= separated_states.separator.size(); i++) {
    std::vector<bool> slots(separated_states.separator.size());
    std::fill(std::begin(slots), std::begin(slots) + i, true);
    do {
      std::vector<uint32_t> separator_states;
      for (int j = 0; j < separated_states.separator.size(); j++) {
        if (slots[j]) {
          separator_states.push_back(separated_states.separator[j]);
        }
      }
      composite_separator_states[CompositeState(separator_states)] =
          qdfa.AddEtaXState();
    } while (std::prev_permutation(std::begin(slots), std::end(slots)));
  }

  for (auto [first_state, first_idx] : composite_separator_states) {
    for (auto [second_state, second_idx] : composite_separator_states) {
      PoolItem<std::vector<uint32_t>> unite_temp = nfa_states_pool.Request();
      absl::c_set_union(first_state, second_state, std::back_inserter(*unite_temp));
      CompositeState result(*unite_temp);
      qdfa.AddEta(first_idx, second_idx, composite_separator_states[result]);
    }
  }

  // Explicitly initialize empty states.
  std::array<uint32_t, K> empty_states;
  for (int i = 0; i < K; i++) {
    empty_states[i] = qdfa.components_[i].AddState();
    qdfa.components_[i].SetEmptyState(empty_states[i]);
    composite_states[i][CompositeState()] = empty_states[i];
    qdfa.components_[i].AddRhoTransition(
        empty_states[i], composite_separator_states[CompositeState()]);
  }

  // Initialize start states.
  std::array<CompositeState, K> start_states;
  {
    PoolItem<std::vector<uint32_t>> nfa_start_states =
        nfa_states_pool.Request();
    nfa_start_states->push_back(nfa.start_state);
    nfa.EpsilonClosure(nfa_start_states.get());
    for (int i = 0; i < K; i++) {
      PoolItem<std::vector<uint32_t>> intersect_temp =
          nfa_states_pool.Request();
      absl::c_set_intersection(*nfa_start_states, parts[i],
                               std::back_inserter(*intersect_temp));
      start_states[i] = CompositeState(*intersect_temp);
      if (composite_states[i].find(start_states[i]) ==
          std::end(composite_states[i])) {
        composite_states[i][start_states[i]] = qdfa.components_[i].AddState();
      }
      qdfa.components_[i].SetStartState(composite_states[i][start_states[i]]);
    }
  }

  std::stack<std::pair<CompositeState, int>> pending;
  for (int i = 0; i < K; i++) {
    pending.push(std::make_pair(start_states[i], i));
  }

  while (!pending.empty()) {
    const auto [state, i] = pending.top();
    pending.pop();
    if (!visited.insert(std::make_pair(state, i)).second) {
      continue;
    }
    if (iterations != nullptr) {
      ++*iterations;
    }

    if (std::binary_search(std::begin(state), std::end(state),
                           nfa.final_state)) {
      qdfa.components_[i].MakeFinalState(composite_states[i][state]);
    }

    for (const char symbol : nfa.alphabet) {
      PoolItem<std::vector<uint32_t>> intersect_temp =
          nfa_states_pool.Request();
      {
        PoolItem<std::vector<uint32_t>> nfa_states = nfa_states_pool.Request();
        nfa.MakeTransitions(state, symbol, nfa_states.get());
        absl::c_set_intersection(*nfa_states, parts[i],
                                 std::back_inserter(*intersect_temp));
      }

      CompositeState tau(*intersect_temp);
      if (composite_states[i].find(tau) == std::end(composite_states[i])) {
        composite_states[i][tau] = qdfa.components_[i].AddState();
      }
      if (!tau.empty()) {
        qdfa.components_[i].AddTauTransition(composite_states[i][state], symbol,
                                             composite_states[i][tau]);
      }

      PoolItem<std::vector<uint32_t>> temp = nfa_states_pool.Request();
      absl::c_set_intersection(tau, separated_states.separator,
                               std::back_inserter(*temp));
      CompositeState rho(*temp);
      qdfa.components_[i].AddRhoTransition(composite_states[i][tau],
                                           composite_separator_states[rho]);

      if (!extended.insert(std::make_pair(tau, i)).second) {
        continue;
      }
      for (const auto& [eta_x, eta_x_idx] : composite_separator_states) {
        PoolItem<std::vector<uint32_t>> nfa_states = nfa_states_pool.Request();
        nfa_states->insert(std::begin(*nfa_states), std::begin(eta_x),
                           std::end(eta_x));
        nfa.EpsilonClosure(nfa_states.get());

        PoolItem<std::vector<uint32_t>> unite_temp = nfa_states_pool.Request();
        PoolItem<std::vector<uint32_t>> intersect_temp =
            nfa_states_pool.Request();
        absl::c_set_intersection(*nfa_states, parts[i],
                                 std::back_inserter(*intersect_temp));
        absl::c_set_union(tau, *intersect_temp, std::back_inserter(*unite_temp));
        CompositeState eta(*unite_temp);
        if (composite_states[i].find(eta) == std::end(composite_states[i])) {
          composite_states[i][eta] = qdfa.components_[i].AddState();
        }
        qdfa.components_[i].AddEtaTransition(
            composite_states[i][tau], eta_x_idx, composite_states[i][eta]);
        auto next_eta = std::make_pair(eta, i);
        if (visited.find(next_eta) == std::end(visited)) {
          pending.push(next_eta);
        }
      }
    }
  }

  return qdfa;
}

}  // namespace sqdfa

#endif  // SQDFA_EAGER_QUASI_DETERMINIZE_H_
