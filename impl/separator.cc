#include "separator.h"

#include <algorithm>
#include <iterator>
#include <variant>

namespace sqdfa {

namespace {

// The weight of the inner states of a subautomaton (all but its start and
// final states, which form the separator if the walk stops there).
uint32_t InnerWeight(const ThompsonNode& node, SeparatorWeight weight) {
  return weight == SeparatorWeight::kStates ? node.states_count - 2
                                            : node.symbols_count;
}

uint32_t Weight(const ThompsonNode& node, SeparatorWeight weight) {
  return weight == SeparatorWeight::kStates ? node.states_count
                                            : node.symbols_count;
}

}  // namespace

uint32_t FindInternal(ThompsonDescription& description, uint32_t node_idx,
                      SeparatorWeight weight) {
  std::stack<uint32_t, std::vector<uint32_t>> past_datas;
  const uint32_t weight_limit =
      (Weight(description.Node(node_idx), weight) * 2) / 3;

  // Descend into the heavier child while the current subautomaton is too
  // heavy. Symbol nodes have no inner states, so the walk stops there.
  while (InnerWeight(description.Node(node_idx), weight) > weight_limit &&
         !std::holds_alternative<SymbolNode>(description.Node(node_idx).node)) {
    past_datas.push(node_idx);
    description.Node(node_idx).Match(
        [](const SymbolNode) {},
        [&](const ConcatNode concat_data) {
          node_idx = Weight(description.Node(concat_data.left_node_idx),
                            weight) >=
                             Weight(description.Node(
                                        concat_data.right_node_idx),
                                    weight)
                         ? concat_data.left_node_idx
                         : concat_data.right_node_idx;
        },
        [&](const UnionNode union_data) {
          node_idx =
              Weight(description.Node(union_data.left_node_idx), weight) >=
                      Weight(description.Node(union_data.right_node_idx),
                             weight)
                  ? union_data.left_node_idx
                  : union_data.right_node_idx;
        },
        [&](const IterNode iter_data) { node_idx = iter_data.node_idx; });
  }

  if (!past_datas.empty()) {
    // Remove the subautomaton at node_idx from its parent. The parent is
    // copied, since adding nodes may reallocate the description.
    const uint32_t parent_idx = past_datas.top();
    const ThompsonNode parent = description.Node(parent_idx);
    parent.Match(
        [](const SymbolNode) {},
        [&](const ConcatNode concat_data) {
          // The parent becomes the remaining child.
          const uint32_t other_idx = concat_data.left_node_idx == node_idx
                                         ? concat_data.right_node_idx
                                         : concat_data.left_node_idx;
          const ThompsonNode other = description.Node(other_idx);
          description.Node(parent_idx).start_state = other.start_state;
          description.Node(parent_idx).final_state = other.final_state;
          description.Node(parent_idx).node = other.node;
        },
        [&](const UnionNode union_data) {
          // The parent keeps its start and final states and the remaining
          // child: s -> other -> f.
          const uint32_t other_idx = union_data.left_node_idx == node_idx
                                         ? union_data.right_node_idx
                                         : union_data.left_node_idx;
          const ThompsonNode other = description.Node(other_idx);
          const uint32_t fake_first_idx = description.AddNode({
              .start_state = parent.start_state,
              .final_state = parent.start_state,
              .states_count = 1,
              .symbols_count = 0,
              .node = SymbolNode{},
          });
          const uint32_t first_concat_idx = description.AddNode({
              .start_state = parent.start_state,
              .final_state = other.final_state,
              .states_count = other.states_count + 1,
              .symbols_count = other.symbols_count,
              .node =
                  ConcatNode{
                      .left_node_idx = fake_first_idx,
                      .right_node_idx = other_idx,
                  },
          });
          const uint32_t fake_second_idx = description.AddNode({
              .start_state = parent.final_state,
              .final_state = parent.final_state,
              .states_count = 1,
              .symbols_count = 0,
              .node = SymbolNode{},
          });
          description.Node(parent_idx).node = ConcatNode{
              .left_node_idx = first_concat_idx,
              .right_node_idx = fake_second_idx,
          };
        },
        [&](const IterNode) {
          // The parent keeps only its start and final states.
          description.Node(parent_idx).node = SymbolNode{};
        });
    do {
      description.Node(past_datas.top()).states_count -=
          description.Node(node_idx).states_count;
      description.Node(past_datas.top()).symbols_count -=
          description.Node(node_idx).symbols_count;
      past_datas.pop();
    } while (!past_datas.empty());
  }

  return node_idx;
}

namespace {

void InsertEssential(const ThompsonDescription& description,
                     const ThompsonNode& node, std::vector<uint32_t>* states) {
  node.Match(
      [&](const SymbolNode) {
        if (node.symbols_count > 0) {
          states->push_back(node.final_state);
        }
      },
      [&](const ConcatNode& concat_data) {
        InsertEssential(description,
                        description.Node(concat_data.left_node_idx), states);
        InsertEssential(description,
                        description.Node(concat_data.right_node_idx), states);
      },
      [&](const UnionNode& union_data) {
        InsertEssential(description,
                        description.Node(union_data.left_node_idx), states);
        InsertEssential(description,
                        description.Node(union_data.right_node_idx), states);
      },
      [&](const IterNode& iter_data) {
        InsertEssential(description, description.Node(iter_data.node_idx),
                        states);
      });
}

}  // namespace

std::vector<uint32_t> EssentialStates(const ThompsonDescription& description) {
  const ThompsonNode& root = description.Node(description.NodeIdx());
  std::vector<uint32_t> states = {root.start_state};
  InsertEssential(description, root, &states);
  std::sort(std::begin(states), std::end(states));
  states.erase(std::unique(std::begin(states), std::end(states)),
               std::end(states));
  return states;
}

void Insert(const ThompsonDescription& description, const ThompsonNode& node,
            std::unordered_set<uint32_t>* outside_states) {
  outside_states->insert(node.start_state);
  outside_states->insert(node.final_state);
  node.Match([](const SymbolNode) {},
             [&](const ConcatNode& concat_data) {
               Insert(description, description.Node(concat_data.left_node_idx),
                      outside_states);
               Insert(description, description.Node(concat_data.right_node_idx),
                      outside_states);
             },
             [&](const UnionNode& union_data) {
               Insert(description, description.Node(union_data.left_node_idx),
                      outside_states);
               Insert(description, description.Node(union_data.right_node_idx),
                      outside_states);
             },
             [&](const IterNode& iter_data) {
               Insert(description, description.Node(iter_data.node_idx),
                      outside_states);
             });
}

}  // namespace sqdfa
