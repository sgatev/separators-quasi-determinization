#include "regex.h"

#include <utility>

#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"

namespace sqdfa {

Regex::Regex(Char regex) : regex_(std::move(regex)) {}

Regex::Regex(Concat regex) : regex_(std::move(regex)) {}

Regex::Regex(Union regex) : regex_(std::move(regex)) {}

Regex::Regex(Iter regex) : regex_(std::move(regex)) {}

Regex::Regex(Times&& regex) : regex_(std::move(regex)) {}

Regex::Regex(Regex&& regex) : regex_(std::move(regex.regex_)) {}

Char::Char(char value) : value_(value) {}

char Char::Value() const { return value_; }

std::vector<Regex*> Union::Regexes() const {
  std::vector<Regex*> regexes;
  for (const auto& regex : regexes_) {
    regexes.push_back(regex.get());
  }
  return regexes;
}

std::vector<Regex*> Concat::Regexes() const {
  std::vector<Regex*> regexes;
  for (const auto& regex : regexes_) {
    regexes.push_back(regex.get());
  }
  return regexes;
}

Iter::Iter(Regex regex) : regex_(std::make_unique<Regex>(std::move(regex))) {}

Regex* Iter::NestedRegex() const { return regex_.get(); }

Times::Times(Regex regex, int times)
    : regex_(std::make_unique<Regex>(std::move(regex))), times_(times) {}

Regex* Times::NestedRegex() const { return regex_.get(); }

int Times::GetTimes() const { return times_; }

std::string RegexToString(const Regex* regex) {
  return regex->Match(
      [](const Char& regex) -> std::string {
        return std::string(1, regex.Value());
      },
      [](const Concat& regex) -> std::string {
        std::vector<std::string> pieces;
        for (const Regex* regex : regex.Regexes()) {
          pieces.push_back(absl::StrCat("(", RegexToString(regex), ")"));
        }
        return absl::StrJoin(pieces, ".");
      },
      [](const Union& regex) -> std::string {
        std::vector<std::string> pieces;
        for (const Regex* regex : regex.Regexes()) {
          pieces.push_back(RegexToString(regex));
        }
        return absl::StrCat("(", absl::StrJoin(pieces, "|"), ")");
      },
      [](const Iter& regex) -> std::string {
        return absl::StrCat("(", RegexToString(regex.NestedRegex()), ")*");
      },
      [](const Times& regex) -> std::string {
        std::vector<std::string> pieces;
        for (int i = 0; i < regex.GetTimes(); i++) {
          pieces.push_back(RegexToString(regex.NestedRegex()));
        }
        return absl::StrCat("(", absl::StrJoin(pieces, "."), ")");
      });
}

}  // namespace sqdfa
