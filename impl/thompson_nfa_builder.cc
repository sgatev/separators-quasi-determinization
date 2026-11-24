#include "thompson_nfa_builder.h"

#include <utility>

#include "types.h"

namespace sqdfa {

std::pair<Nfa, ThompsonDescription> ThompsonNfaBuilder::Build() noexcept {
  nfa_.start_state = description_.Node(description_.NodeIdx()).start_state;
  nfa_.final_state = description_.Node(description_.NodeIdx()).final_state;
  return std::make_pair(nfa_, description_);
}

uint32_t ThompsonNfaBuilder::BuildSymbol(const char symbol) noexcept {
  const uint32_t start_state = nfa_.AddState();
  const uint32_t final_state = nfa_.AddState();

  nfa_.AddTransition(start_state, symbol, final_state);

  return description_.AddNode({
      .start_state = start_state,
      .final_state = final_state,
      .states_count = 2,
      .symbols_count = symbol == '~' || symbol == char_empty ? 0u : 1u,
      .node = SymbolNode{},
  });
}

uint32_t ThompsonNfaBuilder::BuildIter(const uint32_t node_idx) noexcept {
  const uint32_t start_state = nfa_.AddState();
  const uint32_t final_state = nfa_.AddState();

  const ThompsonNode node = description_.Node(node_idx);
  nfa_.AddTransition(start_state, char_empty, node.start_state);
  nfa_.AddTransition(start_state, char_empty, final_state);
  nfa_.AddTransition(node.final_state, char_empty, node.start_state);
  nfa_.AddTransition(node.final_state, char_empty, final_state);

  return description_.AddNode(ThompsonNode{
      .start_state = start_state,
      .final_state = final_state,
      .states_count = node.states_count + 2,
      .symbols_count = node.symbols_count,
      .node =
          IterNode{
              .node_idx = node_idx,
          },
  });
}

uint32_t ThompsonNfaBuilder::BuildUnion(
    const uint32_t left_node_idx, const uint32_t right_node_idx) noexcept {
  const uint32_t start_state = nfa_.AddState();
  const uint32_t final_state = nfa_.AddState();

  const ThompsonNode left_data = description_.Node(left_node_idx);
  const ThompsonNode right_data = description_.Node(right_node_idx);
  nfa_.AddTransition(start_state, char_empty, left_data.start_state);
  nfa_.AddTransition(start_state, char_empty, right_data.start_state);
  nfa_.AddTransition(left_data.final_state, char_empty, final_state);
  nfa_.AddTransition(right_data.final_state, char_empty, final_state);

  return description_.AddNode(ThompsonNode{
      .start_state = start_state,
      .final_state = final_state,
      .states_count = left_data.states_count + right_data.states_count + 2,
      .symbols_count = left_data.symbols_count + right_data.symbols_count,
      .node =
          UnionNode{
              .left_node_idx = left_node_idx,
              .right_node_idx = right_node_idx,
          },
  });
}

uint32_t ThompsonNfaBuilder::BuildConcat(
    const uint32_t left_node_idx, const uint32_t right_node_idx) noexcept {
  const ThompsonNode left_data = description_.Node(left_node_idx);
  const ThompsonNode right_data = description_.Node(right_node_idx);
  nfa_.AddTransition(left_data.final_state, char_empty, right_data.start_state);

  return description_.AddNode(ThompsonNode{
      .start_state = left_data.start_state,
      .final_state = right_data.final_state,
      .states_count = left_data.states_count + right_data.states_count,
      .symbols_count = left_data.symbols_count + right_data.symbols_count,
      .node =
          ConcatNode{
              .left_node_idx = left_node_idx,
              .right_node_idx = right_node_idx,
          },
  });
}

void ThompsonNfaBuilder::Done(const uint32_t node) noexcept {
  description_.SetNodeIdx(node);
}

}  // namespace sqdfa
