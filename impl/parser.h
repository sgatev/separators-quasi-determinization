#ifndef SQDFA_PARSER_H_
#define SQDFA_PARSER_H_

#include <cinttypes>
#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "overload.h"

namespace sqdfa {

enum Operator : uint8_t {
  STAR,
  CONCAT,
  UNION,
  LEFT_PAREN,
  RIGHT_PAREN,
  END,

  COUNT,
};

enum class Action : uint8_t {
  SHIFT,
  REDUCE,
  ACCEPT,
  ERROR_MISSING_OPERATOR,
  ERROR_MISSING_RIGHT_PAREN,
  ERROR_UNBALANCED_RIGHT_PAREN,
};

static const int operators_count = static_cast<int>(Operator::COUNT);

static const Action action_table[operators_count][operators_count] = {
    // *
    {Action::SHIFT, Action::REDUCE, Action::REDUCE, Action::SHIFT,
     Action::REDUCE, Action::REDUCE},

    // .
    {Action::SHIFT, Action::REDUCE, Action::REDUCE, Action::SHIFT,
     Action::REDUCE, Action::REDUCE},

    // |
    {Action::SHIFT, Action::SHIFT, Action::REDUCE, Action::SHIFT,
     Action::REDUCE, Action::REDUCE},

    // (
    {Action::SHIFT, Action::SHIFT, Action::SHIFT, Action::SHIFT, Action::SHIFT,
     Action::ERROR_MISSING_RIGHT_PAREN},

    // )
    {Action::REDUCE, Action::REDUCE, Action::REDUCE,
     Action::ERROR_MISSING_OPERATOR, Action::REDUCE, Action::REDUCE},

    // $
    {Action::SHIFT, Action::SHIFT, Action::SHIFT, Action::SHIFT,
     Action::ERROR_UNBALANCED_RIGHT_PAREN, Action::ACCEPT},
};

template <class ValueType, class BuilderType>
class Parser {
public:
  static std::optional<std::string> Parse(std::string_view regex,
                                          BuilderType* builder) {
    return Parser(regex, builder).Parse();
  }

private:
  Parser(std::string_view regex, BuilderType* builder)
      : regex_(regex), builder_(builder) {
    operators_.push_back(Operator::END);
    ReadToken();
  }

  void ReadToken() {
    if (regex_.empty() || regex_.front() == '\n') {
      token_ = Operator::END;
      return;
    }

    switch (regex_.front()) {
      case '*':
        token_ = Operator::STAR;
        break;
      case '.':
        token_ = Operator::CONCAT;
        break;
      case '|':
        token_ = Operator::UNION;
        break;
      case '(':
        token_ = Operator::LEFT_PAREN;
        break;
      case ')':
        token_ = Operator::RIGHT_PAREN;
        break;
      default:
        token_ = ReadSymbol();
        break;
    }

    regex_.remove_prefix(1);
  }

  ValueType ReadSymbol() { return builder_->BuildSymbol(regex_.front()); }

  std::optional<std::string> Parse() {
    while (true) {
      if (std::holds_alternative<ValueType>(token_)) {
        Shift();
        continue;
      }

      switch (action_table[operators_.back()][std::get<Operator>(token_)]) {
        case Action::SHIFT: {
          Shift();
          break;
        }
        case Action::REDUCE: {
          std::optional<std::string> reduce_error = Reduce();
          if (reduce_error) {
            return reduce_error;
          }
          break;
        }
        case Action::ACCEPT: {
          if (values_.size() != 1) {
            return "syntax error";
          }

          const ValueType value = PopValue();
          builder_->Done(value);
          return std::nullopt;
        }
        case Action::ERROR_MISSING_OPERATOR:
          return "missing operator";
        case Action::ERROR_MISSING_RIGHT_PAREN:
          return "missing closing parenthesis";
        case Action::ERROR_UNBALANCED_RIGHT_PAREN:
          return "unbalanced closing parenthesis";
      }
    }
  }

  void Shift() {
    std::visit(
        Overload([this](const ValueType value) { values_.push_back(value); },
                 [this](const Operator opr) { operators_.push_back(opr); }),
        token_);
    ReadToken();
  }

  std::optional<std::string> Reduce() {
    switch (operators_.back()) {
      case Operator::STAR: {
        if (values_.empty()) {
          return "operator * expects 1 argument";
        }

        const ValueType value = PopValue();
        values_.push_back(builder_->BuildIter(value));
        break;
      }
      case Operator::CONCAT: {
        if (values_.size() < 2) {
          return "operator . expects 2 arguments";
        }

        const ValueType right_value = PopValue();
        const ValueType left_value = PopValue();
        values_.push_back(builder_->BuildConcat(left_value, right_value));
        break;
      }
      case Operator::UNION: {
        if (values_.size() < 2) {
          return "operator | expects 2 arguments";
        }

        const ValueType right_value = PopValue();
        const ValueType left_value = PopValue();
        values_.push_back(builder_->BuildUnion(left_value, right_value));
        break;
      }
      case Operator::RIGHT_PAREN: {
        operators_.pop_back();
        break;
      }
      case Operator::LEFT_PAREN:
        return "should not reduce Operator::LEFT_PAREN";
      case Operator::END:
        return "should not reduce Operator::END";
      case Operator::COUNT:
        return "should not reduce Operator::COUNT";
    }
    operators_.pop_back();
    return std::nullopt;
  }

  ValueType PopValue() {
    const ValueType value = values_.back();
    values_.pop_back();
    return value;
  }

  std::string_view regex_;
  BuilderType* builder_;
  std::vector<Operator> operators_;
  std::vector<ValueType> values_;
  std::variant<Operator, ValueType> token_;
};

}  // namespace sqdfa

#endif  // SQDFA_PARSER_H_
