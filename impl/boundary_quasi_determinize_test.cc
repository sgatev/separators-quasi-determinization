#include "boundary_quasi_determinize.h"

#include <string>
#include <string_view>
#include <utility>

#include "gtest/gtest.h"
#include "nfa.h"
#include "separator.h"
#include "test_util.h"

namespace sqdfa {
namespace {

template <int K>
std::pair<Nfa, BoundaryQdfa<K>> Build(
    std::string_view expression,
    SeparatorWeight weight = SeparatorWeight::kSymbols) {
  auto [nfa, description] = BuildThompsonNfa(expression);
  const SeparatedStates<K> separated_states =
      SeparateStates<K>(description, weight);
  return {nfa, BoundaryQuasiDeterminize<K>(nfa, separated_states)};
}

TEST(BoundaryQuasiDeterminize, Example) {
  const auto [nfa, qdfa] = Build<2>("(0|1)*.0.(0|1)");
  EXPECT_FALSE(qdfa.Match(""));
  EXPECT_FALSE(qdfa.Match("0"));
  EXPECT_FALSE(qdfa.Match("10"));
  EXPECT_TRUE(qdfa.Match("101"));
  EXPECT_TRUE(qdfa.Match("0101101"));
  EXPECT_FALSE(qdfa.Match("10111"));
}

TEST(BoundaryQuasiDeterminize, BoundariesCoverSeparator) {
  auto [nfa, description] = BuildThompsonNfa("(0|1)*.0.(0|1).(0|1).(0|1)");
  const SeparatedStates<4> separated_states = SeparateStates<4>(description);
  const auto boundaries = ComputeBoundaries<4>(nfa, separated_states);
  for (uint32_t x : separated_states.separator) {
    bool covered = false;
    for (const auto& boundary : boundaries) {
      covered = covered || std::binary_search(std::begin(boundary),
                                              std::end(boundary), x);
    }
    EXPECT_TRUE(covered) << x;
  }
}

template <int K>
void ExpectAgreesWithNfa(SeparatorWeight weight) {
  for (const std::string& expression : RandomTestExpressions(40)) {
    const auto [nfa, qdfa] = Build<K>(expression, weight);
    for (const std::string& word : AllWords("01", 10)) {
      EXPECT_EQ(qdfa.Match(word), nfa.Match(word))
          << K << " components, weight " << static_cast<int>(weight)
          << ", expression \"" << expression << "\", word \"" << word << "\"";
    }
  }
}

TEST(BoundaryQuasiDeterminize, AgreesWithNfa) {
  for (SeparatorWeight weight :
       {SeparatorWeight::kStates, SeparatorWeight::kSymbols}) {
    ExpectAgreesWithNfa<2>(weight);
    ExpectAgreesWithNfa<3>(weight);
    ExpectAgreesWithNfa<4>(weight);
    ExpectAgreesWithNfa<6>(weight);
    ExpectAgreesWithNfa<8>(weight);
  }
}

}  // namespace
}  // namespace sqdfa
