#ifndef SQDFA_COMPOSITE_STATE_H_
#define SQDFA_COMPOSITE_STATE_H_

#include <algorithm>
#include <cinttypes>
#include <cstddef>
#include <iterator>
#include <memory>
#include <utility>

#include "absl/base/attributes.h"
#include "absl/hash/hash.h"

namespace sqdfa {

// Automaton state constructed from a set of NFA states.
struct CompositeState {
 public:
  CompositeState() noexcept : size_(0) {}

  template <class Container>
  explicit CompositeState(const Container& nfa_states) noexcept
      : size_(std::size(nfa_states)),
        data_(new uint32_t[std::size(nfa_states)],
              std::default_delete<uint32_t[]>()) {
    std::copy(std::begin(nfa_states), std::end(nfa_states), begin());
  }

  ABSL_MUST_USE_RESULT bool operator==(const CompositeState& other) const
      noexcept {
    return std::equal(begin(), end(), std::begin(other), std::end(other));
  }

  // Returns a hash of the composite state.
  template <typename H>
  friend ABSL_MUST_USE_RESULT H
  AbslHashValue(H h, const CompositeState& composite_state) noexcept {
    return H::combine_contiguous(
        H::combine(std::move(h), std::size(composite_state)),
        composite_state.data_.get(), std::size(composite_state));
  }

  // Returns the number of NFA states.
  ABSL_MUST_USE_RESULT std::size_t size() const noexcept { return size_; }

  // Returns true if there are no NFA states.
  ABSL_MUST_USE_RESULT bool empty() const noexcept { return size_ == 0; }

  // Returns an iterator to the beginning of the NFA states.
  ABSL_MUST_USE_RESULT uint32_t* const begin() const noexcept {
    return data_.get();
  }

  // Returns an iterator to the end of the NFA states.
  ABSL_MUST_USE_RESULT uint32_t* const end() const noexcept {
    return data_.get() + size_;
  }

 private:
  std::size_t size_;
  std::shared_ptr<uint32_t> data_;
};

}  // namespace sqdfa

#endif  // SQDFA_COMPOSITE_STATE_H_
