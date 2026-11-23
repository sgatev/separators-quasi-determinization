#ifndef SQDFA_POOL_H_
#define SQDFA_POOL_H_

#include <functional>
#include <memory>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "absl/base/attributes.h"

namespace sqdfa {

// Item retrieved from a pool.
template <typename T>
class PoolItem {
 public:
  PoolItem(std::unique_ptr<T> item,
           std::function<void(std::unique_ptr<T>)> release)
      : item_(std::move(item)), release_(release) {}

  PoolItem(const PoolItem&) = default;
  PoolItem(PoolItem&&) = default;

  ~PoolItem() { release_(std::move(item_)); }

  ABSL_MUST_USE_RESULT typename std::add_lvalue_reference<T>::type operator*()
      const noexcept {
    return *item_;
  }

  ABSL_MUST_USE_RESULT T* operator->() const noexcept {
    return item_.operator->();
  }

  ABSL_MUST_USE_RESULT T* get() const noexcept { return item_.get(); }

 private:
  std::unique_ptr<T> item_;
  std::function<void(std::unique_ptr<T>)> release_;
};

// Pool of reusable objects.
template <typename T, typename... Args>
class Pool {
 public:
  Pool(
      Args... args, std::function<void(T*)> clear = [](T*) {})
      : args_(std::make_tuple(args...)), clear_(clear) {}

  Pool(const Pool& other) : args_(other.args_), clear_(other.clear_) {}

  Pool(Pool&& other) = default;

  Pool& operator=(const Pool& other) noexcept {
    *this = Pool(other);
    return *this;
  }

  Pool& operator=(Pool&&) noexcept = default;

  // Requests a new object from the pool.
  ABSL_MUST_USE_RESULT PoolItem<T> Request() {
    std::unique_ptr<T> item;
    if (items_.empty()) {
      item = std::make_unique<T>(std::move(std::make_from_tuple<T>(args_)));
    } else {
      item = std::move(items_.back());
      items_.pop_back();
    }
    return PoolItem<T>(std::move(item), [this](std::unique_ptr<T> item) {
      clear_(item.get());
      items_.push_back(std::move(item));
    });
  }

 private:
  std::tuple<Args...> args_;
  std::function<void(T*)> clear_;
  std::vector<std::unique_ptr<T>> items_;
};

}  // namespace sqdfa

#endif  // SQDFA_POOL_H_
