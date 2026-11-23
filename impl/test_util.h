#ifndef SQDFA_TEST_UTIL_H_
#define SQDFA_TEST_UTIL_H_

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
  };
  return expressions;
}

}  // namespace sqdfa

#endif  // SQDFA_TEST_UTIL_H_
