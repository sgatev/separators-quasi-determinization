// Matching throughput of the finite-state devices of the thesis.
//
// Every device is converted to dense arrays before matching, so that all of
// them pay one array access per table look-up. The NFA is simulated with bit
// sets of states. Each measurement matches a random word over the alphabet of
// the expression in full; the median of several runs is reported.

#include <algorithm>
#include <array>
#include <chrono>
#include <cinttypes>
#include <cstdio>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "boundary_quasi_determinize.h"
#include "determinize.h"
#include "dfa.h"
#include "eager_quasi_determinize.h"
#include "nfa.h"
#include "parser.h"
#include "qdfa.h"
#include "regex.h"
#include "separator.h"
#include "thompson_description.h"
#include "thompson_nfa_builder.h"

namespace sqdfa {
namespace {

constexpr int kRuns = 7;
constexpr size_t kInputSize = 4 << 20;
constexpr size_t kCheckWords = 2000;

// Maps the symbols of the alphabet to 0, 1, ...
struct Alphabet {
  explicit Alphabet(const Nfa& nfa)
      : symbols(std::begin(nfa.alphabet), std::end(nfa.alphabet)) {
    std::sort(std::begin(symbols), std::end(symbols));
    index.fill(-1);
    for (size_t s = 0; s < symbols.size(); s++) {
      index[static_cast<unsigned char>(symbols[s])] = s;
    }
  }

  std::vector<char> symbols;
  std::array<int, 256> index;
};

// NFA simulation with bit sets: next[state][symbol] is the epsilon closure of
// the symbol successors of state.
class BitSetNfa {
 public:
  BitSetNfa(const Nfa& nfa, const Alphabet& alphabet)
      : alphabet_(alphabet),
        words_((nfa.StatesCount() + 63) / 64),
        start_(words_),
        final_(words_),
        next_(nfa.StatesCount() * alphabet.symbols.size() * words_) {
    std::vector<uint32_t> start = {nfa.start_state};
    nfa.EpsilonClosure(&start);
    for (uint32_t state : start) Set(start_.data(), state);
    Set(final_.data(), nfa.final_state);
    for (uint32_t state = 0; state < nfa.StatesCount(); state++) {
      for (size_t s = 0; s < alphabet.symbols.size(); s++) {
        std::vector<uint32_t> from = {state};
        std::vector<uint32_t> to;
        nfa.MakeTransitions(from, alphabet.symbols[s], &to);
        for (uint32_t target : to) Set(Row(state, s), target);
      }
    }
  }

  bool Match(std::string_view input) const {
    std::vector<uint64_t> current = start_;
    std::vector<uint64_t> next(words_);
    for (char symbol : input) {
      const int s = alphabet_.index[static_cast<unsigned char>(symbol)];
      if (s < 0) return false;
      std::fill(std::begin(next), std::end(next), 0);
      for (size_t w = 0; w < words_; w++) {
        for (uint64_t bits = current[w]; bits != 0; bits &= bits - 1) {
          const uint32_t state = w * 64 + __builtin_ctzll(bits);
          const uint64_t* row = Row(state, s);
          for (size_t v = 0; v < words_; v++) next[v] |= row[v];
        }
      }
      std::swap(current, next);
    }
    for (size_t w = 0; w < words_; w++) {
      if (current[w] & final_[w]) return true;
    }
    return false;
  }

 private:
  static void Set(uint64_t* bits, uint32_t state) {
    bits[state / 64] |= uint64_t{1} << (state % 64);
  }
  uint64_t* Row(uint32_t state, size_t s) {
    return next_.data() + (state * alphabet_.symbols.size() + s) * words_;
  }
  const uint64_t* Row(uint32_t state, size_t s) const {
    return next_.data() + (state * alphabet_.symbols.size() + s) * words_;
  }

  const Alphabet& alphabet_;
  size_t words_;
  std::vector<uint64_t> start_;
  std::vector<uint64_t> final_;
  std::vector<uint64_t> next_;
};

// A DFA as a dense table. Missing transitions lead to a dead state.
class DenseDfa {
 public:
  DenseDfa(const Dfa& dfa, const Alphabet& alphabet)
      : alphabet_(alphabet), size_(alphabet.symbols.size()) {
    const uint32_t dead = dfa.StatesCount();
    next_.resize((dfa.StatesCount() + 1) * size_, dead);
    final_.resize(dfa.StatesCount() + 1, false);
    for (uint32_t state = 0; state < dfa.StatesCount(); state++) {
      final_[state] = dfa.IsFinal(state);
      for (size_t s = 0; s < size_; s++) {
        const uint32_t target = dfa.Next(state, alphabet.symbols[s]);
        if (target != uint32_null) next_[state * size_ + s] = target;
      }
    }
    start_ = dfa.StartState();
  }

  bool Match(std::string_view input) const {
    uint32_t state = start_;
    for (char symbol : input) {
      const int s = alphabet_.index[static_cast<unsigned char>(symbol)];
      if (s < 0) return false;
      state = next_[state * size_ + s];
    }
    return final_[state];
  }

 private:
  const Alphabet& alphabet_;
  size_t size_;
  uint32_t start_;
  std::vector<uint32_t> next_;
  std::vector<bool> final_;
};

// A QDFA of Algorithm quasi_det_sfsa_components as dense tables, with the
// tabulated separator extension function eta_x.
template <int K>
class DenseQdfa {
 public:
  DenseQdfa(const Qdfa<K>& qdfa, const Alphabet& alphabet)
      : alphabet_(alphabet), size_(alphabet.symbols.size()) {
    separators_ = qdfa.state_etas_.size();
    eta_x_.resize(separators_ * separators_);
    for (uint32_t x = 0; x < separators_; x++) {
      for (uint32_t y = 0; y < separators_; y++) {
        eta_x_[x * separators_ + y] =
            FindTransitionTarget(qdfa.etas_, qdfa.state_etas_[x], y);
      }
    }
    for (int i = 0; i < K; i++) {
      const QdfaComponent& component = qdfa.components_[i];
      Component& dense = components_[i];
      const uint32_t states = component.StatesCount();
      dense.start = component.StartState();
      dense.tau.resize(states * size_);
      dense.rho.resize(states);
      dense.eta.resize(states * separators_);
      dense.final.resize(states);
      for (uint32_t state = 0; state < states; state++) {
        dense.final[state] = component.IsFinal(state);
        dense.rho[state] = component.MakeRhoTransition(state);
        for (size_t s = 0; s < size_; s++) {
          dense.tau[state * size_ + s] =
              component.MakeTauTransition(state, alphabet.symbols[s]);
        }
        for (uint32_t x = 0; x < separators_; x++) {
          dense.eta[state * separators_ + x] =
              component.MakeEtaTransition(state, x);
        }
      }
    }
  }

  bool Match(std::string_view input) const {
    std::array<uint32_t, K> state;
    for (int i = 0; i < K; i++) state[i] = components_[i].start;
    for (char symbol : input) {
      const int s = alphabet_.index[static_cast<unsigned char>(symbol)];
      if (s < 0) return false;
      std::array<uint32_t, K> tau;
      for (int i = 0; i < K; i++) {
        tau[i] = components_[i].tau[state[i] * size_ + s];
      }
      uint32_t x = components_[0].rho[tau[0]];
      for (int i = 1; i < K; i++) {
        x = eta_x_[x * separators_ + components_[i].rho[tau[i]]];
      }
      for (int i = 0; i < K; i++) {
        state[i] = components_[i].eta[tau[i] * separators_ + x];
      }
    }
    for (int i = 0; i < K; i++) {
      if (components_[i].final[state[i]]) return true;
    }
    return false;
  }

 private:
  struct Component {
    uint32_t start;
    std::vector<uint32_t> tau;
    std::vector<uint32_t> rho;
    std::vector<uint32_t> eta;
    std::vector<bool> final;
  };

  const Alphabet& alphabet_;
  size_t size_;
  uint32_t separators_;
  std::vector<uint32_t> eta_x_;
  std::array<Component, K> components_;
};

std::string RandomWord(const Alphabet& alphabet, size_t length,
                       std::mt19937_64& random) {
  std::uniform_int_distribution<size_t> pick(0, alphabet.symbols.size() - 1);
  std::string word(length, ' ');
  for (char& c : word) c = alphabet.symbols[pick(random)];
  return word;
}

// Returns the median throughput in MB/s, or nullopt if the matcher disagrees
// with the reference on the check words or the input.
std::optional<double> Measure(const std::function<bool(std::string_view)>& match,
                              const std::function<bool(std::string_view)>& reference,
                              const std::vector<std::string>& check_words,
                              const std::string& input) {
  for (const std::string& word : check_words) {
    if (match(word) != reference(word)) return std::nullopt;
  }
  std::vector<double> rates;
  bool result = false;
  for (int run = 0; run < kRuns; run++) {
    const auto begin = std::chrono::steady_clock::now();
    result ^= match(input);
    const auto end = std::chrono::steady_clock::now();
    const double seconds = std::chrono::duration<double>(end - begin).count();
    rates.push_back(input.size() / seconds / 1e6);
  }
  if (result != (kRuns % 2 == 1 && reference(input))) return std::nullopt;
  std::sort(std::begin(rates), std::end(rates));
  return rates[kRuns / 2];
}

void Report(const std::string& name, const std::string& size,
            const std::optional<double>& rate) {
  std::printf("  %-22s %12s  ", name.c_str(), size.c_str());
  if (rate) {
    std::printf("%10.1f MB/s\n", *rate);
  } else {
    std::printf("%10s\n", "MISMATCH");
  }
}

template <int K>
void RunQdfa(const Nfa& nfa, const ThompsonDescription& description,
             const Alphabet& alphabet, const BitSetNfa& reference,
             const std::vector<std::string>& check_words,
             const std::string& input) {
  const SeparatedStates<K> separated = SeparateStates<K>(description);
  Nfa closed = nfa;
  const Qdfa<K> qdfa = EagerQuasiDeterminize<K>(closed, separated);
  const DenseQdfa<K> dense(qdfa, alphabet);
  Report(std::to_string(K) + "-QDFA''", std::to_string(qdfa.StatesCount()),
         Measure([&](std::string_view w) { return dense.Match(w); },
                 [&](std::string_view w) { return reference.Match(w); },
                 check_words, input));
}

template <int K>
void RunBoundaryQdfa(const Nfa& nfa, const ThompsonDescription& description,
                     const BitSetNfa& reference,
                     const std::vector<std::string>& check_words,
                     const std::string& input) {
  const SeparatedStates<K> separated = SeparateStates<K>(description);
  const BoundaryQdfa<K> qdfa = BoundaryQuasiDeterminize<K>(nfa, separated);
  Report(std::to_string(K) + "-QDFA^b", std::to_string(qdfa.StatesCount()),
         Measure([&](std::string_view w) { return qdfa.Match(w); },
                 [&](std::string_view w) { return reference.Match(w); },
                 check_words, input));
}

void Run(const std::string& expression, bool with_dfa) {
  ThompsonNfaBuilder builder;
  const auto parse_error =
      Parser<uint32_t, ThompsonNfaBuilder>::Parse(expression, &builder);
  if (parse_error) {
    std::cout << "error: " << *parse_error << std::endl;
    return;
  }
  const auto [nfa, description] = builder.Build();
  const Alphabet alphabet(nfa);

  std::mt19937_64 random(42);
  std::vector<std::string> check_words;
  std::uniform_int_distribution<size_t> length(0, 40);
  for (size_t w = 0; w < kCheckWords; w++) {
    check_words.push_back(RandomWord(alphabet, length(random), random));
  }
  const std::string input = RandomWord(alphabet, kInputSize, random);

  std::cout << "expression: " << expression << " (" << nfa.StatesCount()
            << " NFA states, input " << (kInputSize >> 20) << " MiB)"
            << std::endl;
  std::printf("  %-22s %12s  %15s\n", "device", "states", "throughput");

  const BitSetNfa reference(nfa, alphabet);
  Report("NFA (bit sets)", std::to_string(nfa.StatesCount()),
         Measure([&](std::string_view w) { return reference.Match(w); },
                 [&](std::string_view w) { return reference.Match(w); },
                 check_words, input));
  if (with_dfa) {
    const Dfa dfa = Determinize(nfa);
    const DenseDfa dense(dfa, alphabet);
    Report("DFA", std::to_string(dfa.StatesCount()),
           Measure([&](std::string_view w) { return dense.Match(w); },
                   [&](std::string_view w) { return reference.Match(w); },
                   check_words, input));
  }
  RunQdfa<2>(nfa, description, alphabet, reference, check_words, input);
  RunQdfa<3>(nfa, description, alphabet, reference, check_words, input);
  RunBoundaryQdfa<2>(nfa, description, reference, check_words, input);
  RunBoundaryQdfa<4>(nfa, description, reference, check_words, input);
  RunBoundaryQdfa<8>(nfa, description, reference, check_words, input);
  RunBoundaryQdfa<16>(nfa, description, reference, check_words, input);
  std::cout << std::endl;
}

Union BinaryUnion() { return Union(Char('0'), Char('1')); }

Union LatinAlphabetUnion() {
  return Union({
      Char('a'), Char('b'), Char('c'), Char('d'), Char('e'), Char('f'),
      Char('g'), Char('h'), Char('i'), Char('j'), Char('k'), Char('l'),
      Char('m'), Char('n'), Char('o'), Char('p'), Char('q'), Char('r'),
      Char('s'), Char('t'), Char('u'), Char('v'), Char('w'), Char('x'),
      Char('y'), Char('z'),
  });
}

// The expressions are built as in main.cc, so that the devices are the same
// as in the thesis' tables.
std::string BinaryTail(int n) {
  Regex regex = Concat(Iter(BinaryUnion()), Char('0'), Times(BinaryUnion(), n));
  return RegexToString(&regex);
}

std::string Latin() {
  Regex regex = Concat(LatinAlphabetUnion(), Iter(LatinAlphabetUnion()));
  return RegexToString(&regex);
}

}  // namespace
}  // namespace sqdfa

int main() {
  sqdfa::Run(sqdfa::BinaryTail(16), true);
  sqdfa::Run(sqdfa::BinaryTail(20), true);
  sqdfa::Run(sqdfa::BinaryTail(24), false);
  sqdfa::Run(sqdfa::Latin(), true);
  return 0;
}
