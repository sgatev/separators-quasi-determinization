#include <algorithm>
#include <chrono>
#include <cinttypes>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <optional>
#include <ratio>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "boundary_quasi_determinize.h"
#include "determinize.h"
#include "dfa.h"
#include "eager_quasi_determinize.h"
#include "epsilon.h"
#include "nfa.h"
#include "parser.h"
#include "qdfa.h"
#include "quasi_determinize.h"
#include "regex.h"
#include "separator.h"
#include "thompson_description.h"
#include "thompson_nfa_builder.h"
#include "timer.h"

namespace sqdfa {
namespace {

using namespace std::chrono_literals;

Timer MakeTimer(const std::string_view description) {
  return Timer(
      [description](std::chrono::duration<uint64_t, std::nano> elapsed_time) {
        std::cout << "[timer] " << description << ": ";
        if (elapsed_time >= 1s) {
          std::cout << std::chrono::duration_cast<std::chrono::seconds>(
                           elapsed_time)
                           .count()
                    << "s";
        } else if (elapsed_time >= 1ms) {
          std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(
                           elapsed_time)
                           .count()
                    << "ms";
        } else if (elapsed_time >= 1us) {
          std::cout << std::chrono::duration_cast<std::chrono::microseconds>(
                           elapsed_time)
                           .count()
                    << "us";
        } else {
          std::cout << elapsed_time.count() << "ns";
        }
        std::cout << std::endl;
      });
}

}  // namespace

std::pair<Nfa, ThompsonDescription> RunNfa(const std::string_view expression) {
  const Timer timer = MakeTimer("NFA construction");

  ThompsonNfaBuilder builder;
  const std::optional<std::string> parse_error =
      Parser<uint32_t, ThompsonNfaBuilder>::Parse(expression, &builder);
  if (parse_error) {
    std::cout << "error: " << *parse_error << std::endl;
    return std::make_pair(Nfa(), ThompsonDescription());
  }

  auto [nfa, description] = builder.Build();
  std::cout << "nfa: " << nfa.StatesCount() << " states, "
            << nfa.TransitionsCount() << " transitions" << std::endl;
  return std::make_pair(nfa, description);
}

void RunDfa(const Nfa& nfa) {
  const Timer timer = MakeTimer("DFA construction");

  const Dfa dfa = Determinize(nfa);
  std::cout << "dfa: " << dfa.StatesCount() << " states, "
            << dfa.TransitionsCount() << " transitions" << std::endl;
}

const char* WeightName(SeparatorWeight weight) {
  return weight == SeparatorWeight::kStates ? "states" : "symbols";
}

// Prints |X| and, for every component, |Q_i| and the number m_i of essential
// states in Q_i. The component quasi-states are bounded by 2^(m_i + |X|).
template <int K>
void PrintSeparator(const ThompsonDescription& description,
                    const SeparatedStates<K>& separated_states) {
  const std::vector<uint32_t> essential = EssentialStates(description);
  std::cout << "separator: |X| = " << separated_states.separator.size();
  for (int i = 0; i < K; i++) {
    uint32_t states = 0;
    uint32_t essential_states = 0;
    for (uint32_t state : separated_states.components[i]) {
      if (std::binary_search(std::begin(separated_states.separator),
                             std::end(separated_states.separator), state)) {
        continue;
      }
      states++;
      if (std::binary_search(std::begin(essential), std::end(essential),
                             state)) {
        essential_states++;
      }
    }
    std::cout << ", |Q_" << i + 1 << "| = " << states << ", m_" << i + 1
              << " = " << essential_states;
  }
  std::cout << " (m = " << essential.size() - 1 << ")" << std::endl;
}

template <int K>
SeparatedStates<K> RunSeparator(const ThompsonDescription& description,
                                SeparatorWeight weight) {
  SeparatedStates<K> separated_states;
  {
    const Timer timer = MakeTimer("separator construction");
    separated_states = SeparateStates<K>(description, weight);
  }
  std::cout << "weight: " << WeightName(weight) << std::endl;
  PrintSeparator<K>(description, separated_states);
  return separated_states;
}

template <int K>
void RunQdfa(Nfa nfa, ThompsonDescription description,
             SeparatorWeight weight) {
  static_assert(K >= 1, "number of QDFA components has to be at least 1");

  const SeparatedStates<K> separated_states =
      RunSeparator<K>(description, weight);

  const Timer timer = MakeTimer("QDFA construction");
  uint64_t iterations = 0;
  const Qdfa<K> qdfa = QuasiDeterminize<K>(nfa, separated_states, &iterations);
  std::cout << K << "-qdfa: " << qdfa.StatesCount() << " states, "
            << qdfa.TransitionsCount() << " transitions, " << iterations
            << " iterations" << std::endl;
}

template <int K>
void RunEagerQdfa(Nfa nfa, ThompsonDescription description,
                  SeparatorWeight weight) {
  static_assert(K >= 1, "number of QDFA components has to be at least 1");

  const SeparatedStates<K> separated_states =
      RunSeparator<K>(description, weight);

  ComputeEpsilonClosure(&nfa);

  Timer timer = MakeTimer("eager QDFA construction");
  uint64_t iterations = 0;
  const Qdfa<K> qdfa =
      EagerQuasiDeterminize<K>(nfa, separated_states, &iterations);
  std::cout << K << "-eager-qdfa: " << qdfa.StatesCount() << " states, "
            << qdfa.TransitionsCount() << " transitions, " << iterations
            << " iterations" << std::endl;
}

template <int K>
void RunBoundaryQdfa(Nfa nfa, ThompsonDescription description,
                     SeparatorWeight weight) {
  const SeparatedStates<K> separated_states =
      RunSeparator<K>(description, weight);
  const auto boundaries = ComputeBoundaries<K>(nfa, separated_states);
  std::cout << "boundaries:";
  for (const auto& boundary : boundaries) {
    std::cout << " " << boundary.size();
  }
  std::cout << std::endl;

  const Timer timer = MakeTimer("boundary QDFA construction");
  uint64_t iterations = 0;
  const BoundaryQdfa<K> qdfa =
      BoundaryQuasiDeterminize<K>(nfa, separated_states, &iterations);
  std::cout << K << "-boundary-qdfa: " << qdfa.StatesCount() << " states, "
            << qdfa.TransitionsCount() << " transitions, " << iterations
            << " iterations" << std::endl;
}

template <int... Ks>
void RunBoundaryQdfas(const Nfa& nfa, const ThompsonDescription& description,
                      SeparatorWeight weight) {
  ((RunBoundaryQdfa<Ks>(nfa, description, weight), std::cout << std::endl),
   ...);
}

Union LatinAlphabetUnion() {
  return Union({
      Char('a'), Char('b'), Char('c'), Char('d'), Char('e'), Char('f'),
      Char('g'), Char('h'), Char('i'), Char('j'), Char('k'), Char('l'),
      Char('m'), Char('n'), Char('o'), Char('p'), Char('q'), Char('r'),
      Char('s'), Char('t'), Char('u'), Char('v'), Char('w'), Char('x'),
      Char('y'), Char('z'),
  });
}

Union DigitsUnion() {
  return Union({
      Char('0'),
      Char('1'),
      Char('2'),
      Char('3'),
      Char('4'),
      Char('5'),
      Char('6'),
      Char('7'),
      Char('8'),
      Char('9'),
  });
}

Union BinaryUnion() { return Union(Char('0'), Char('1')); }

Union Maybe(Regex regex) { return Union(regex, Char('~')); }

void Run() {
  // The expressions of the comparison tables in the thesis.
  std::vector<Regex> regexes;
  regexes.emplace_back(Concat(
      Char('a'), Char('b'), Char('c'), Char('d'), Char('e'), Char('f'),
      Char('g'), Char('h'), Char('i'), Char('j'), Char('k'), Char('l'),
      Char('m'), Char('n'), Char('o'), Char('p'), Char('q'), Char('r'),
      Char('s'), Char('t'), Char('u'), Char('v'), Char('w'), Char('x'),
      Char('y'), Char('z')));
  regexes.emplace_back(
      Concat(LatinAlphabetUnion(), Iter(LatinAlphabetUnion())));
  regexes.emplace_back(Concat(Maybe(Char('0')), Maybe(Char('1')),
                              Maybe(Char('2')), Maybe(Char('3')),
                              Maybe(Char('4')), Maybe(Char('5')),
                              Maybe(Char('6')), Maybe(Char('7')),
                              Maybe(Char('8')), Maybe(Char('9'))));
  regexes.emplace_back(
      Concat(Iter(BinaryUnion()), Char('0'), Times(BinaryUnion(), 16)));
  // A larger instance of the previous expression.
  regexes.emplace_back(
      Concat(Iter(BinaryUnion()), Char('0'), Times(BinaryUnion(), 20)));

  for (const Regex& regex : regexes) {
    const std::string expression = RegexToString(&regex);
    std::cout << "expression: " << expression << std::endl;
    std::cout << std::endl;

    auto [nfa, description] = RunNfa(expression);
    std::cout << std::endl;

    RunDfa(nfa);
    std::cout << std::endl;

    for (SeparatorWeight weight :
         {SeparatorWeight::kStates, SeparatorWeight::kSymbols}) {
      RunQdfa<2>(nfa, description, weight);
      std::cout << std::endl;

      RunEagerQdfa<2>(nfa, description, weight);
      std::cout << std::endl;

      RunQdfa<3>(nfa, description, weight);
      std::cout << std::endl;

      RunEagerQdfa<3>(nfa, description, weight);
      std::cout << std::endl;

      RunBoundaryQdfas<2, 3, 4, 6, 8, 12, 16>(nfa, description, weight);
    }
  }
}

}  // namespace sqdfa

int main() {
  sqdfa::Run();
  return 0;
}
