#include "separator.h"

#include <set>
#include <string>
#include <vector>

#include "gtest/gtest.h"
#include "nfa.h"
#include "test_util.h"

namespace sqdfa {
namespace {

// Checks that the separation is a partition {X, Q_1, ..., Q_K} of the states
// with no transitions between different components, and that every component
// contains the separator states it shares transitions with.
template <int K>
void ExpectValidSeparation(const std::string& expression,
                           SeparatorWeight weight) {
  auto [nfa, description] = BuildThompsonNfa(expression);
  const SeparatedStates<K> separated = SeparateStates<K>(description, weight);
  const std::set<uint32_t> separator(std::begin(separated.separator),
                                     std::end(separated.separator));
  std::vector<int> component(nfa.StatesCount(), -1);
  for (int i = 0; i < K; i++) {
    for (uint32_t state : separated.components[i]) {
      if (separator.count(state)) continue;
      EXPECT_EQ(component[state], -1)
          << "state " << state << " in two components, expression "
          << expression << ", K = " << K;
      component[state] = i;
    }
  }
  for (uint32_t state = 0; state < nfa.StatesCount(); state++) {
    EXPECT_TRUE(separator.count(state) || component[state] != -1)
        << "state " << state << " uncovered, expression " << expression
        << ", K = " << K;
  }
  for (uint32_t from = 0; from < nfa.StatesCount(); from++) {
    for (uint32_t t = nfa.state_transitions_[from]; t != uint32_null;
         t = nfa.transitions_[t].next) {
      const uint32_t to = nfa.transitions_[t].target;
      if (component[from] != -1 && component[to] != -1) {
        EXPECT_EQ(component[from], component[to])
            << "transition " << from << " -> " << to << ", expression "
            << expression << ", K = " << K;
      }
    }
  }
}

template <int... Ks>
void ExpectValidSeparations(const std::string& expression,
                            SeparatorWeight weight) {
  (ExpectValidSeparation<Ks>(expression, weight), ...);
}

TEST(SeparateStates, PartitionsTheStates) {
  std::vector<std::string> expressions = RandomTestExpressions(200);
  expressions.push_back("(a|b|c|d|e|f|g|h).(a|b|c|d|e|f|g|h)*");
  expressions.push_back("(a.b.c.d.e.f.g.h)");
  for (const std::string& expression : expressions) {
    for (SeparatorWeight weight :
         {SeparatorWeight::kStates, SeparatorWeight::kSymbols}) {
      ExpectValidSeparations<2, 3, 4, 6, 8, 16>(expression, weight);
    }
  }
}

}  // namespace
}  // namespace sqdfa
