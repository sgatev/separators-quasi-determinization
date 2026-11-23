#ifndef SQDFA_QUASI_DETERMINIZE_H_
#define SQDFA_QUASI_DETERMINIZE_H_

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

// Constructs a quas-deterministic finite-state automaton from a finite-state
// automaton.
template <int K>
ABSL_MUST_USE_RESULT Qdfa<K> QuasiDeterminize(
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
  absl::flat_hash_set<std::array<CompositeState, K>> visited;

  Qdfa<K> qdfa;

  // Explicitly initialize empty states.
  for (int i = 0; i < K; i++) {
    const uint32_t empty_state = qdfa.components_[i].AddState();
    qdfa.components_[i].SetEmptyState(empty_state);
    composite_states[i][CompositeState()] = empty_state;
  }
  composite_separator_states[CompositeState()] = qdfa.AddEtaXState();

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

  std::stack<std::array<CompositeState, K>> pending;
  pending.push(start_states);

  while (!pending.empty()) {
    const std::array<CompositeState, K> state = pending.top();
    pending.pop();
    if (!visited.insert(state).second) {
      continue;
    }
    if (iterations != nullptr) {
      ++*iterations;
    }

    for (int i = 0; i < K; i++) {
      if (std::binary_search(std::begin(state[i]), std::end(state[i]),
                             nfa.final_state)) {
        qdfa.components_[i].MakeFinalState(composite_states[i][state[i]]);
      }
    }

    for (const char symbol : nfa.alphabet) {
      std::array<CompositeState, K> tau;
      for (int i = 0; i < K; i++) {
        PoolItem<std::vector<uint32_t>> nfa_states = nfa_states_pool.Request();
        nfa.MakeTransitions(state[i], symbol, nfa_states.get());

        PoolItem<std::vector<uint32_t>> intersect_temp =
            nfa_states_pool.Request();
        absl::c_set_intersection(*nfa_states, parts[i],
                                 std::back_inserter(*intersect_temp));
        tau[i] = CompositeState(*intersect_temp);

        if (composite_states[i].find(tau[i]) == std::end(composite_states[i])) {
          composite_states[i][tau[i]] = qdfa.components_[i].AddState();
        }

        if (tau[i].empty()) {
          continue;
        }
        qdfa.components_[i].AddTauTransition(
            composite_states[i][state[i]], symbol, composite_states[i][tau[i]]);
      }

      std::array<CompositeState, K> rho;
      for (int i = 0; i < K; i++) {
        PoolItem<std::vector<uint32_t>> intersect_temp =
            nfa_states_pool.Request();
        absl::c_set_intersection(tau[i], separated_states.separator,
                                 std::back_inserter(*intersect_temp));
        rho[i] = CompositeState(*intersect_temp);
        if (composite_separator_states.find(rho[i]) ==
            std::end(composite_separator_states)) {
          composite_separator_states[rho[i]] = qdfa.AddEtaXState();
        }
        qdfa.components_[i].AddRhoTransition(
            composite_states[i][tau[i]], composite_separator_states[rho[i]]);
      }

      CompositeState eta_x = rho[0];
      for (int i = 1; i < K; i++) {
        PoolItem<std::vector<uint32_t>> unite_temp = nfa_states_pool.Request();
        absl::c_set_union(eta_x, rho[i], std::back_inserter(*unite_temp));
        CompositeState next_eta_x(*unite_temp);
        if (composite_separator_states.find(next_eta_x) ==
            std::end(composite_separator_states)) {
          composite_separator_states[next_eta_x] = qdfa.AddEtaXState();
        }
        qdfa.AddEta(composite_separator_states[eta_x],
                    composite_separator_states[rho[i]],
                    composite_separator_states[next_eta_x]);
        eta_x = next_eta_x;
      }

      PoolItem<std::vector<uint32_t>> nfa_states = nfa_states_pool.Request();
      nfa_states->insert(std::begin(*nfa_states), std::begin(eta_x),
                         std::end(eta_x));
      nfa.EpsilonClosure(nfa_states.get());
      std::array<CompositeState, K> eta;
      for (int i = 0; i < K; i++) {
        PoolItem<std::vector<uint32_t>> unite_temp = nfa_states_pool.Request();
        PoolItem<std::vector<uint32_t>> intersect_temp =
            nfa_states_pool.Request();
        absl::c_set_intersection(*nfa_states, parts[i],
                                 std::back_inserter(*intersect_temp));
        absl::c_set_union(tau[i], *intersect_temp, std::back_inserter(*unite_temp));
        eta[i] = CompositeState(*unite_temp);
        if (composite_states[i].find(eta[i]) == std::end(composite_states[i])) {
          composite_states[i][eta[i]] = qdfa.components_[i].AddState();
        }
        qdfa.components_[i].AddEtaTransition(composite_states[i][tau[i]],
                                             composite_separator_states[eta_x],
                                             composite_states[i][eta[i]]);
      }
      if (visited.find(eta) == std::end(visited)) {
        pending.push(eta);
      }
    }
  }

  return qdfa;
}

}  // namespace sqdfa

#endif  // SQDFA_QUASI_DETERMINIZE_H_
