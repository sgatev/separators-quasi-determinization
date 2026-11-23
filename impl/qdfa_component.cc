#include "qdfa_component.h"

namespace sqdfa {

uint32_t QdfaComponent::AddState() {
  const uint32_t state = state_taus_.size();
  state_taus_.push_back(uint32_null);
  state_etas_.push_back(uint32_null);
  rhos_.push_back(uint32_null);
  final_states_.push_back(false);
  return state;
}

void QdfaComponent::SetStartState(uint32_t state) { start_state_ = state; }

void QdfaComponent::SetEmptyState(uint32_t state) { empty_state_ = state; }

void QdfaComponent::MakeFinalState(uint32_t state) {
  final_states_[state] = true;
}

bool QdfaComponent::IsFinal(uint32_t state) const {
  return final_states_[state];
}

void QdfaComponent::AddTauTransition(uint32_t from, char symbol, uint32_t to) {
  if (FindTransitionTarget(taus_, state_taus_[from], symbol) != uint32_null) {
    return;
  }
  taus_.emplace_back(state_taus_[from], to, symbol);
  state_taus_[from] = taus_.size() - 1;
}

uint32_t QdfaComponent::MakeTauTransition(uint32_t from,
                                          uint32_t symbol) const {
  uint32_t to = FindTransitionTarget(taus_, state_taus_[from], symbol);
  if (to == uint32_null) {
    to = empty_state_;
  }
  return to;
}

void QdfaComponent::AddRhoTransition(uint32_t tau, uint32_t rho) {
  rhos_[tau] = rho;
}

uint32_t QdfaComponent::MakeRhoTransition(uint32_t from) const {
  return rhos_[from];
}

void QdfaComponent::AddEtaTransition(uint32_t tau, uint32_t eta,
                                     uint32_t first_eta) {
  if (FindTransitionTarget(etas_, state_etas_[tau], eta) != uint32_null) {
    return;
  }
  etas_.emplace_back(state_etas_[tau], first_eta, eta);
  state_etas_[tau] = etas_.size() - 1;
}

uint32_t QdfaComponent::MakeEtaTransition(uint32_t from, uint32_t value) const {
  uint32_t to = FindTransitionTarget(etas_, state_etas_[from], value);
  if (to == uint32_null) {
    to = empty_state_;
  }
  return to;
}

uint32_t QdfaComponent::StartState() const { return start_state_; }

uint32_t QdfaComponent::StatesCount() const { return state_taus_.size(); }

uint32_t QdfaComponent::TransitionsCount() const {
  return taus_.size() + etas_.size();
}

}  // namespace sqdfa
