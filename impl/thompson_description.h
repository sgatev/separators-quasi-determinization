#ifndef SQDFA_THOMPSON_DESCRIPTION_H_
#define SQDFA_THOMPSON_DESCRIPTION_H_

#include <cinttypes>
#include <utility>
#include <variant>

#include "types.h"

namespace sqdfa {

struct SymbolNode {};

struct ConcatNode {
  uint32_t left_node_idx;
  uint32_t right_node_idx;
};

struct UnionNode {
  uint32_t left_node_idx;
  uint32_t right_node_idx;
};

struct IterNode {
  uint32_t node_idx;
};

struct ThompsonNode {
  uint32_t start_state;
  uint32_t final_state;
  uint32_t states_count;
  // Number of transitions labelled with a symbol of the alphabet (not epsilon).
  uint32_t symbols_count;
  std::variant<SymbolNode, ConcatNode, UnionNode, IterNode> node;

  template <class... M>
  constexpr auto Match(M&&... matchers) const& {
    return std::visit(Overload(std::forward<M>(matchers)...), node);
  }
};

// The measure that Algorithm thompson_separator balances between the
// components: the number of states, or the number of symbol transitions (the
// essential states, which bound the number of quasi-states).
enum class SeparatorWeight { kStates, kSymbols };

class ThompsonDescription {
 public:
  ThompsonDescription() noexcept : node_idx_(uint32_null) {}

  uint32_t AddNode(ThompsonNode node) noexcept {
    uint32_t node_idx = nodes_.size();
    nodes_.push_back(node);
    return node_idx;
  }

  void SetNodeIdx(uint32_t node_idx) { node_idx_ = node_idx; }

  ThompsonNode& Node(uint32_t idx) noexcept { return nodes_[idx]; }

  ThompsonNode Node(uint32_t idx) const noexcept { return nodes_[idx]; }

  uint32_t NodeIdx() const noexcept { return node_idx_; }

  uint32_t NodesCount() const noexcept { return nodes_.size(); }

 private:
  std::vector<ThompsonNode> nodes_;
  uint32_t node_idx_;
};

}  // namespace sqdfa

#endif  // SQDFA_THOMPSON_DESCRIPTION_H_
