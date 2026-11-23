#include "determinize.h"

#include <algorithm>
#include <cinttypes>
#include <iterator>
#include <stack>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "composite_state.h"
#include "pool.h"

namespace sqdfa {

Dfa Determinize(const Nfa& nfa) {
  Dfa dfa;

  absl::flat_hash_map<CompositeState, uint32_t> composite_states;
  Pool<std::vector<uint32_t>> nfa_states_pool(
      [](std::vector<uint32_t>* states) { states->clear(); });
  std::stack<CompositeState> pending;

  {
    PoolItem<std::vector<uint32_t>> nfa_start_states =
        nfa_states_pool.Request();
    nfa_start_states->push_back(nfa.start_state);
    nfa.EpsilonClosure(nfa_start_states.get());

    const CompositeState start_state(*nfa_start_states);
    composite_states[start_state] = dfa.AddState();
    dfa.SetStartState(composite_states[start_state]);
    pending.push(start_state);
  }

  while (!pending.empty()) {
    const CompositeState state = pending.top();
    pending.pop();

    if (std::binary_search(std::begin(state), std::end(state),
                           nfa.final_state)) {
      dfa.MakeFinalState(composite_states[state]);
    }

    for (const char symbol : nfa.alphabet) {
      PoolItem<std::vector<uint32_t>> next_nfa_states =
          nfa_states_pool.Request();
      nfa.MakeTransitions(state, symbol, next_nfa_states.get());

      const CompositeState next_state(*next_nfa_states);
      if (next_state.empty()) {
        continue;
      }

      if (composite_states.find(next_state) == composite_states.end()) {
        pending.push(next_state);
        composite_states[next_state] = dfa.AddState();
      }

      dfa.AddTransition(composite_states[state], symbol,
                        composite_states[next_state]);
    }
  }

  return dfa;
}

}  // namespace sqdfa
