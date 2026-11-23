#ifndef SQDFA_REGEX_H_
#define SQDFA_REGEX_H_

#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "overload.h"

namespace sqdfa {

class Regex;

class Char {
 public:
  Char(char value);

  char Value() const;

 private:
  char value_;
};

class Concat {
 public:
  template <typename... Regexes>
  Concat(Regexes&&... regexes) {
    (regexes_.push_back(std::make_unique<Regex>(std::move(regexes))), ...);
  }

  std::vector<Regex*> Regexes() const;

 private:
  std::vector<std::unique_ptr<Regex>> regexes_;
};

class Union {
 public:
  template <typename... Regexes>
  Union(Regexes&&... regexes) {
    (regexes_.push_back(std::make_unique<Regex>(std::move(regexes))), ...);
  }

  std::vector<Regex*> Regexes() const;

 private:
  std::vector<std::unique_ptr<Regex>> regexes_;
};

class Iter {
 public:
  Iter(Regex regex);

  Regex* NestedRegex() const;

 private:
  std::unique_ptr<Regex> regex_;
};

class Times {
 public:
  Times(Regex regex, int times);

  Regex* NestedRegex() const;
  int GetTimes() const;

 private:
  std::unique_ptr<Regex> regex_;
  int times_;
};

class Regex {
 public:
  Regex(Char regex);
  Regex(Concat regex);
  Regex(Union regex);
  Regex(Iter regex);
  Regex(Times&& regex);

  Regex(Regex&& regex);

  template <class... M>
  constexpr auto Match(M&&... matchers) const& {
    return std::visit(Overload(std::forward<M>(matchers)...), regex_);
  }

 private:
  std::variant<Char, Concat, Union, Iter, Times> regex_;
};

std::string RegexToString(const Regex* regex);

}  // namespace sqdfa

#endif  // SQDFA_REGEX_H_
