#include "quasi_determinize.h"

#include <string>
#include <string_view>
#include <utility>

#include "epsilon.h"
#include "gtest/gtest.h"
#include "nfa.h"
#include "qdfa.h"
#include "separator.h"
#include "test_util.h"

namespace sqdfa {
namespace {

template <int K>
std::pair<Nfa, Qdfa<K>> Build(
    std::string_view expression,
    SeparatorWeight weight = SeparatorWeight::kSymbols) {
  auto [nfa, description] = BuildThompsonNfa(expression);
  const SeparatedStates<K> separated_states =
      SeparateStates<K>(description, weight);
  
  return {nfa, QuasiDeterminize<K>(nfa, separated_states)};
}

TEST(QuasiDeterminize, Example) {
  const auto [nfa, qdfa] = Build<2>("(0|1)*.0.(0|1)");
  EXPECT_FALSE(qdfa.Match(""));
  EXPECT_FALSE(qdfa.Match("0"));
  EXPECT_FALSE(qdfa.Match("10"));
  EXPECT_TRUE(qdfa.Match("101"));
  EXPECT_TRUE(qdfa.Match("0101101"));
  EXPECT_FALSE(qdfa.Match("10111"));
}

template <int K>
void ExpectAgreesWithNfa(SeparatorWeight weight) {
  for (std::string_view expression : TestExpressions()) {
    const auto [nfa, qdfa] = Build<K>(expression, weight);
    for (const std::string& word : AllWords("01", 10)) {
      EXPECT_EQ(qdfa.Match(word), nfa.Match(word))
          << K << " components, weight " << static_cast<int>(weight)
          << ", expression " << expression << ", word \""
          << word << "\"";
    }
  }
}

TEST(QuasiDeterminize, AgreesWithNfa2) {
  ExpectAgreesWithNfa<2>(SeparatorWeight::kStates);
  ExpectAgreesWithNfa<2>(SeparatorWeight::kSymbols);
}
TEST(QuasiDeterminize, AgreesWithNfa3) {
  ExpectAgreesWithNfa<3>(SeparatorWeight::kStates);
  ExpectAgreesWithNfa<3>(SeparatorWeight::kSymbols);
}

}  // namespace
}  // namespace sqdfa
