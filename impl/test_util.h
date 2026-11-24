#ifndef SQDFA_TEST_UTIL_H_
#define SQDFA_TEST_UTIL_H_

#include <random>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "gtest/gtest.h"
#include "nfa.h"
#include "parser.h"
#include "thompson_description.h"
#include "thompson_nfa_builder.h"

namespace sqdfa {

// Builds the Thompson automaton of a regular expression.
inline std::pair<Nfa, ThompsonDescription> BuildThompsonNfa(
    std::string_view expression) {
  ThompsonNfaBuilder builder;
  const auto parse_error =
      Parser<uint32_t, ThompsonNfaBuilder>::Parse(expression, &builder);
  EXPECT_FALSE(parse_error.has_value()) << *parse_error;
  return builder.Build();
}

// Returns all words over the alphabet of length at most max_length.
inline std::vector<std::string> AllWords(std::string_view alphabet,
                                         int max_length) {
  std::vector<std::string> words = {""};
  for (size_t begin = 0, end = 1; max_length > 0; max_length--) {
    for (size_t i = begin; i < end; i++) {
      for (char symbol : alphabet) {
        words.push_back(words[i] + symbol);
      }
    }
    begin = end;
    end = words.size();
  }
  return words;
}

// Regular expressions used to cross-check the constructions against the NFA.
inline const std::vector<std::string_view>& TestExpressions() {
  static const std::vector<std::string_view> expressions = {
      "(0|1)*.0.(0|1)",
      "(0|1)*.0.(0|1).(0|1).(0|1)",
      "(0|~).(1|~).(0|~).(1|~)",
      "(0.1|1.0)*.(0|1)*",
      "((0|1).(0|1))*.1",
      "(0|1|0.1|1.0).(0|1|0.1|1.0)*",
      "((0|1).((0.1)|(1|0.0))*)|(1.(0|1))*",
  };
  return expressions;
}

// Returns a random fully parenthesized regular expression over {0, 1, ~}.
inline std::string RandomExpression(std::mt19937& random, int depth) {
  std::uniform_int_distribution<int> pick(0, depth <= 0 ? 2 : 6);
  switch (pick(random)) {
    case 0:
      return "0";
    case 1:
      return "1";
    case 2:
      return depth <= 0 ? "~" : "0";
    case 3:
    case 4:
      return "(" + RandomExpression(random, depth - 1) + "." +
             RandomExpression(random, depth - 1) + ")";
    case 5:
      return "(" + RandomExpression(random, depth - 1) + "|" +
             RandomExpression(random, depth - 1) + ")";
    default:
      return "(" + RandomExpression(random, depth - 1) + ")*";
  }
}

// Random expressions followed by the fixed test expressions.
inline std::vector<std::string> RandomTestExpressions(int count) {
  std::mt19937 random(7);
  std::vector<std::string> expressions;
  for (int i = 0; i < count; i++) {
    expressions.push_back(RandomExpression(random, 6));
  }
  for (std::string_view expression : TestExpressions()) {
    expressions.emplace_back(expression);
  }
  return expressions;
}

}  // namespace sqdfa

#endif  // SQDFA_TEST_UTIL_H_
