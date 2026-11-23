#ifndef SQDFA_TIMER_H_
#define SQDFA_TIMER_H_

#include <chrono>
#include <cinttypes>
#include <functional>
#include <ratio>

namespace sqdfa {

// RAII class that reports the elapsed time of a scope.
class Timer {
  // Reports the elapsed time produced by a Timer.
  using TimeReporter =
      std::function<void(std::chrono::duration<uint64_t, std::nano>)>;

 public:
  Timer(const TimeReporter report) noexcept
      : report_(report), start_(std::chrono::system_clock::now()) {}

  ~Timer() noexcept { report_(std::chrono::system_clock::now() - start_); }

  Timer(const Timer&) = delete;
  Timer& operator=(const Timer&) = delete;
  Timer(Timer&&) = delete;
  Timer& operator=(Timer&&) = delete;

 private:
  const TimeReporter report_;
  const std::chrono::time_point<std::chrono::system_clock> start_;
};

}  // namespace sqdfa

#endif  // SQDFA_TIMER_H_
