#include "determinize.h"

#include <string>
#include <string_view>

#include "dfa.h"
#include "gtest/gtest.h"
#include "test_util.h"

namespace sqdfa {
namespace {

TEST(Determinize, Example) {
  const auto [nfa, description] = BuildThompsonNfa("(0|1)*.0.(0|1)");
  const Dfa dfa = Determinize(nfa);
  EXPECT_FALSE(dfa.Match(""));
  EXPECT_FALSE(dfa.Match("0"));
  EXPECT_FALSE(dfa.Match("10"));
  EXPECT_TRUE(dfa.Match("101"));
  EXPECT_TRUE(dfa.Match("0101101"));
  EXPECT_FALSE(dfa.Match("10111"));
}

TEST(Determinize, AgreesWithNfa) {
  for (std::string_view expression : TestExpressions()) {
    const auto [nfa, description] = BuildThompsonNfa(expression);
    const Dfa dfa = Determinize(nfa);
    for (const std::string& word : AllWords("01", 10)) {
      EXPECT_EQ(dfa.Match(word), nfa.Match(word))
          << "expression " << expression << ", word \"" << word << "\"";
    }
  }
}

}  // namespace
}  // namespace sqdfa
