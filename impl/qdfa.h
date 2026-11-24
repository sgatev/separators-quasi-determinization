#ifndef SQDFA_QDFA_H_
#define SQDFA_QDFA_H_

#include <array>
#include <cinttypes>
#include <string_view>
#include <vector>

#include "qdfa_component.h"
#include "transitions.h"
#include "types.h"

namespace sqdfa {

template <int K>
class Qdfa {
 public:
  uint32_t AddEtaXState() {
    const uint32_t state = state_etas_.size();
    state_etas_.push_back(uint32_null);
    return state;
  }

  void AddEta(uint32_t first_rho, uint32_t second_rho, uint32_t eta) {
    if (FindTransitionTarget(etas_, state_etas_[first_rho], second_rho) !=
        uint32_null) {
      return;
    }

    etas_.emplace_back(state_etas_[first_rho], eta, second_rho);
    state_etas_[first_rho] = etas_.size() - 1;
  }

  bool Match(const std::string_view input) const {
    std::array<uint32_t, K> state;
    for (int i = 0; i < K; i++) {
      state[i] = components_[i].StartState();
    }

    for (char symbol : input) {
      std::array<uint32_t, K> tau;
      bool dead = true;
      for (int i = 0; i < K; i++) {
        tau[i] = components_[i].MakeTauTransition(state[i], symbol);
        dead = dead && tau[i] == components_[i].EmptyState();
      }
      // No state of the NFA is reached, for example because the symbol is
      // not in the alphabet. The tables have no entries for this case.
      if (dead) {
        return false;
      }

      std::array<uint32_t, K> rho;
      for (int i = 0; i < K; i++) {
        rho[i] = components_[i].MakeRhoTransition(tau[i]);
      }

      uint32_t eta_x = rho[0];
      for (int i = 1; i < K; i++) {
        eta_x = FindTransitionTarget(etas_, state_etas_[eta_x], rho[i]);
      }

      for (int i = 0; i < K; i++) {
        state[i] = components_[i].MakeEtaTransition(tau[i], eta_x);
      }
    }

    for (int i = 0; i < K; i++) {
      if (components_[i].IsFinal(state[i])) {
        return true;
      }
    }
    return false;
  }

  uint32_t StatesCount() const {
    uint32_t result = 0;
    for (int i = 0; i < K; i++) {
      result += components_[i].StatesCount();
    }
    return result;
  }

  uint32_t TransitionsCount() const {
    uint32_t result = etas_.size();
    for (int i = 0; i < K; i++) {
      result += components_[i].TransitionsCount();
    }
    return result;
  }

  std::array<QdfaComponent, K> components_;
  std::vector<Transition<uint32_t>> etas_;
  std::vector<uint32_t> state_etas_;
};

}  // namespace sqdfa

#endif  // SQDFA_QDFA_H_
