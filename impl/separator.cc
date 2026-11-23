#include "separator.h"

namespace sqdfa {

uint32_t FindInternal(ThompsonDescription& description, uint32_t node_idx) {
  std::stack<uint32_t, std::vector<uint32_t>> past_datas;
  const uint32_t states_count_limit =
      (description.Node(node_idx).states_count * 2) / 3;
  uint32_t inside_states_count = description.Node(node_idx).states_count - 2;
  uint32_t outside_states_count = 0;

  while (inside_states_count > states_count_limit) {
    past_datas.push(node_idx);
    description.Node(node_idx).Match(
        [](const SymbolNode) {},
        [&](const ConcatNode concat_data) {
          const ThompsonNode left_data =
              description.Node(concat_data.left_node_idx);
          const ThompsonNode right_data =
              description.Node(concat_data.right_node_idx);

          if (left_data.states_count >= right_data.states_count) {
            node_idx = concat_data.left_node_idx;
            outside_states_count += right_data.states_count;
          } else {
            node_idx = concat_data.right_node_idx;
            outside_states_count += left_data.states_count;
          }

          inside_states_count = description.Node(node_idx).states_count - 2;
        },
        [&](const UnionNode union_data) {
          const ThompsonNode left_data =
              description.Node(union_data.left_node_idx);
          const ThompsonNode right_data =
              description.Node(union_data.right_node_idx);

          if (left_data.states_count >= right_data.states_count) {
            node_idx = union_data.left_node_idx;
            outside_states_count += right_data.states_count + 2;
          } else {
            node_idx = union_data.right_node_idx;
            outside_states_count += left_data.states_count + 2;
          }

          inside_states_count = description.Node(node_idx).states_count - 2;
        },
        [&](const IterNode iter_data) {
          node_idx = iter_data.node_idx;
          inside_states_count = description.Node(node_idx).states_count - 2;
          outside_states_count += 2;
        });
  }

  if (!past_datas.empty()) {
    description.Node(past_datas.top())
        .Match([](const SymbolNode) {},
               [&](const ConcatNode concat_data) {
                 const ThompsonNode left_data =
                     description.Node(concat_data.left_node_idx);
                 const ThompsonNode right_data =
                     description.Node(concat_data.right_node_idx);

                 if (left_data.states_count >= right_data.states_count) {
                   description.Node(past_datas.top()).start_state =
                       description.Node(concat_data.right_node_idx).start_state;
                   description.Node(past_datas.top()).final_state =
                       description.Node(concat_data.right_node_idx).final_state;
                   description.Node(past_datas.top()).node =
                       description.Node(concat_data.right_node_idx).node;
                 } else {
                   description.Node(past_datas.top()).start_state =
                       description.Node(concat_data.left_node_idx).start_state;
                   description.Node(past_datas.top()).final_state =
                       description.Node(concat_data.left_node_idx).final_state;
                   description.Node(past_datas.top()).node =
                       description.Node(concat_data.left_node_idx).node;
                 }
               },
               [&](const UnionNode union_data) {
                 const ThompsonNode left_data =
                     description.Node(union_data.left_node_idx);
                 const ThompsonNode right_data =
                     description.Node(union_data.right_node_idx);

                 if (left_data.states_count >= right_data.states_count) {
                   uint32_t fake_first_idx = description.NodesCount();
                   description.AddNode({
                       .start_state = description.Node(node_idx).start_state,
                       .final_state = description.Node(node_idx).start_state,
                       .states_count = 1,
                       .node = SymbolNode{},
                   });

                   uint32_t first_concat_idx = description.NodesCount();
                   description.AddNode({
                       .start_state = description.Node(node_idx).start_state,
                       .final_state = right_data.final_state,
                       .states_count = right_data.states_count + 1,
                       .node =
                           ConcatNode{
                               .left_node_idx = fake_first_idx,
                               .right_node_idx = union_data.right_node_idx,
                           },
                   });

                   uint32_t fake_second_idx = description.NodesCount();
                   description.AddNode({
                       .start_state = description.Node(node_idx).final_state,
                       .final_state = description.Node(node_idx).final_state,
                       .states_count = 1,
                       .node = SymbolNode{},
                   });

                   description.Node(node_idx).node = ConcatNode{
                       .left_node_idx = first_concat_idx,
                       .right_node_idx = fake_second_idx,
                   };
                 } else {
                   uint32_t fake_first_idx = description.NodesCount();
                   description.AddNode({
                       .start_state = description.Node(node_idx).start_state,
                       .final_state = description.Node(node_idx).start_state,
                       .states_count = 1,
                       .node = SymbolNode{},
                   });

                   uint32_t first_concat_idx = description.NodesCount();
                   description.AddNode({
                       .start_state = description.Node(node_idx).start_state,
                       .final_state = left_data.final_state,
                       .states_count = left_data.states_count + 1,
                       .node =
                           ConcatNode{
                               .left_node_idx = fake_first_idx,
                               .right_node_idx = union_data.left_node_idx,
                           },
                   });

                   uint32_t fake_second_idx = description.NodesCount();
                   description.AddNode({
                       .start_state = description.Node(node_idx).final_state,
                       .final_state = description.Node(node_idx).final_state,
                       .states_count = 1,
                       .node = SymbolNode{},
                   });

                   description.Node(node_idx).node = ConcatNode{
                       .left_node_idx = first_concat_idx,
                       .right_node_idx = fake_second_idx,
                   };
                 }
               },
               [&](const IterNode iter_data) {
                 description.Node(past_datas.top()).node = SymbolNode{};
               });
    do {
      description.Node(past_datas.top()).states_count -=
          description.Node(node_idx).states_count;
      past_datas.pop();
    } while (!past_datas.empty());
  }

  return node_idx;
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
