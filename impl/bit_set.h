#ifndef SQDFA_BIT_SET_H_
#define SQDFA_BIT_SET_H_

#include <algorithm>
#include <cinttypes>
#include <cstdlib>
#include <utility>

#include "absl/base/attributes.h"

namespace sqdfa {

// A set of bits.
class BitSet {
 public:
  // Initializes the given number of bits to false.
  explicit BitSet(std::size_t count) noexcept {
    blocks_count_ = count / block_size_ + 1;
    blocks_ = static_cast<uint8_t*>(std::calloc(blocks_count_, block_size_));
  }

  BitSet(const BitSet& other) noexcept {
    blocks_count_ = other.blocks_count_;
    blocks_ = static_cast<uint8_t*>(std::malloc(blocks_count_ * block_size_));
    std::copy(other.blocks_, other.blocks_ + blocks_count_, blocks_);
  }

  BitSet(BitSet&& other) noexcept
      : blocks_(std::exchange(other.blocks_, nullptr)),
        blocks_count_(other.blocks_count_) {}

  BitSet& operator=(const BitSet& other) noexcept {
    *this = BitSet(other);
    return *this;
  }

  BitSet& operator=(BitSet&& other) noexcept {
    std::free(blocks_);
    blocks_ = std::exchange(other.blocks_, nullptr);
    blocks_count_ = other.blocks_count_;
    return *this;
  }

  ~BitSet() noexcept { std::free(blocks_); }

  // Sets a bit at index to true.
  void Set(std::size_t idx) noexcept {
    blocks_[BlockIndex(idx)] |= BitMask(idx);
  }

  // Sets a bit at index to false.
  void Unset(std::size_t idx) noexcept {
    blocks_[BlockIndex(idx)] &= ~BitMask(idx);
  }

  // Sets all bits to false.
  void Reset() noexcept { std::fill(blocks_, blocks_ + blocks_count_, 0); }

  // Tests the value of a bit at index.
  ABSL_MUST_USE_RESULT bool Test(std::size_t idx) const noexcept {
    return blocks_[BlockIndex(idx)] & BitMask(idx);
  }

 private:
  constexpr static std::size_t BlockIndex(std::size_t idx) noexcept {
    return idx / block_size_;
  }

  constexpr static std::size_t BitIndex(std::size_t idx) noexcept {
    return idx % block_size_;
  }

  constexpr static uint8_t BitMask(std::size_t idx) noexcept {
    return uint8_t(1) << BitIndex(idx);
  }

  constexpr static std::size_t block_size_ = sizeof(uint8_t);

  uint8_t* blocks_;
  std::size_t blocks_count_;
};

}  // namespace sqdfa

#endif  // SQDFA_BIT_SET_H_
