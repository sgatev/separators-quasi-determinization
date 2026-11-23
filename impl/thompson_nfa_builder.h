#ifndef SQDFA_THOMPSON_NFA_BUILDER_H_
#define SQDFA_THOMPSON_NFA_BUILDER_H_

#include <cinttypes>
#include <utility>
#include <vector>

#include "nfa.h"
#include "thompson_description.h"
#include "transitions.h"

namespace sqdfa {

class ThompsonNfaBuilder {
 public:
  std::pair<Nfa, ThompsonDescription> Build() noexcept;

  uint32_t BuildSymbol(const char symbol) noexcept;

  uint32_t BuildIter(const uint32_t data_idx) noexcept;

  uint32_t BuildUnion(const uint32_t left_data_idx,
                      const uint32_t right_data_idx) noexcept;

  uint32_t BuildConcat(const uint32_t left_data_idx,
                       const uint32_t right_data_idx) noexcept;

  void Done(const uint32_t data) noexcept;

 private:
  Nfa nfa_;
  ThompsonDescription description_;
};

}  // namespace sqdfa

#endif  // SQDFA_THOMPSON_NFA_BUILDER_H_
