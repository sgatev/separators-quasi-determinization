#ifndef SQDFA_DFA_H_
#define SQDFA_DFA_H_

#include <cinttypes>
#include <string_view>
#include <vector>

#include "transitions.h"

#include "absl/base/attributes.h"

namespace sqdfa {

// A deterministic finite-state automaton.
class Dfa {
 public:
  // Returns true if input is contained in the language of the finite-state
  // automaton.
  ABSL_MUST_USE_RESULT bool Match(const std::string_view input) const;

  // Adds a state to the automaton and returns its index.
  ABSL_MUST_USE_RESULT uint32_t AddState();

  // Adds a transition to the automaton.
  void AddTransition(uint32_t from, char symbol, uint32_t to);

  // Sets the start state of the automaton.
  void SetStartState(uint32_t state);

  // Makes a state of the automaton final.
  void MakeFinalState(uint32_t state);

  // Returns the number of states of the finite-state automaton.
  ABSL_MUST_USE_RESULT uint32_t StatesCount() const;

  // Returns the number of transitions of the finite-state automaton.
  ABSL_MUST_USE_RESULT uint32_t TransitionsCount() const;

 private:
  std::vector<uint32_t> state_transitions_;
  std::vector<Transition<char>> transitions_;
  uint32_t start_state_;
  std::vector<bool> final_states_;
};

}  // namespace sqdfa

#endif  // SQDFA_DFA_H_
