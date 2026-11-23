#ifndef SQDFA_TYPES_H_
#define SQDFA_TYPES_H_

#include <cinttypes>
#include <limits>

namespace sqdfa {

// A uint32_t null value.
constexpr uint32_t uint32_null = std::numeric_limits<uint32_t>::max();

// A char value representing the empty word.
constexpr char char_empty = 0;

}  // namespace sqdfa

#endif  // SQDFA_TYPES_H_
