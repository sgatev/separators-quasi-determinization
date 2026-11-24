#ifndef SQDFA_QDFA_COMPONENT_H_
#define SQDFA_QDFA_COMPONENT_H_

#include <cinttypes>
#include <vector>

#include "absl/base/attributes.h"
#include "transitions.h"
#include "types.h"

namespace sqdfa {

// A component of a quasi-deterministic finite-state automaton.
class QdfaComponent {
 public:
  // Adds a state to the component and returns its index.
  ABSL_MUST_USE_RESULT uint32_t AddState();

  // Sets the start state of the component.
  void SetStartState(uint32_t state);

  // Sets the empty state of the component.
  void SetEmptyState(uint32_t state);

  // Makes a state of the component final.
  void MakeFinalState(uint32_t state);

  // Returns true if the state is marked as final.
  ABSL_MUST_USE_RESULT bool IsFinal(uint32_t state) const;

  // Adds a tau transition to the component.
  void AddTauTransition(uint32_t from, char symbol, uint32_t to);

  // Makes a tau transition from state with symbol.
  ABSL_MUST_USE_RESULT uint32_t MakeTauTransition(uint32_t from,
                                                  uint32_t symbol) const;

  // Adds a rho transition to the component.
  void AddRhoTransition(uint32_t state, uint32_t rho);

  // Makes a rho transition from state.
  ABSL_MUST_USE_RESULT uint32_t MakeRhoTransition(uint32_t from) const;

  // Adds an eta transition to the component.
  void AddEtaTransition(uint32_t from, uint32_t value, uint32_t to);

  // Makes an eta transition from state with value.
  ABSL_MUST_USE_RESULT uint32_t MakeEtaTransition(uint32_t from,
                                                  uint32_t value) const;

  // Returns the empty state of the component.
  ABSL_MUST_USE_RESULT uint32_t EmptyState() const { return empty_state_; }

  // Returns the start state of the component.
  ABSL_MUST_USE_RESULT uint32_t StartState() const;

  // Returns the number of states of the component.
  ABSL_MUST_USE_RESULT uint32_t StatesCount() const;

  // Returns the number of transitions of the component.
  ABSL_MUST_USE_RESULT uint32_t TransitionsCount() const;

 private:
  std::vector<uint32_t> state_taus_;
  std::vector<Transition<char>> taus_;
  std::vector<uint32_t> rhos_;
  std::vector<uint32_t> state_etas_;
  std::vector<Transition<uint32_t>> etas_;
  std::vector<bool> final_states_;
  uint32_t start_state_;
  uint32_t empty_state_;
};

}  // namespace sqdfa

#endif  // SQDFA_QDFA_COMPONENT_H_
