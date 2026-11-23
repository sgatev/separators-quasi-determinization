#ifndef SQDFA_OVERLOAD_H_
#define SQDFA_OVERLOAD_H_

#include <utility>

namespace sqdfa {

template <class... Ts>
struct Overloaded;

template <class T>
struct Overloaded<T> : T {
  Overloaded(T&& t) noexcept : T(std::forward<T>(t)) {}
  using T::operator();
};

template <class T, class... Ts>
struct Overloaded<T, Ts...> : T, Overloaded<Ts...> {
  Overloaded(T&& t, Ts&&... ts) noexcept
      : T(std::forward<T>(t)), Overloaded<Ts...>(std::forward<Ts>(ts)...) {}
  using T::operator();
  using Overloaded<Ts...>::operator();
};

template <class... Ts>
constexpr auto Overload(Ts&&... ts) noexcept {
  return Overloaded<Ts...>(std::forward<Ts>(ts)...);
}

}  // namespace sqdfa

#endif  // SQDFA_OVERLOAD_H_
