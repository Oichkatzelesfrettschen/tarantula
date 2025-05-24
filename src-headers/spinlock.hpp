#ifndef SPINLOCK_HPP
#define SPINLOCK_HPP

#include "spinlock.h"
#include <utility>

class SpinLock {
public:
    constexpr SpinLock() : lock_(SPINLOCK_INITIALIZER) {}
    void lock() noexcept { spinlock_lock(&lock_); }
    bool try_lock() noexcept { return spinlock_trylock(&lock_); }
    void unlock() noexcept { spinlock_unlock(&lock_); }
    spinlock_t* native_handle() noexcept { return &lock_; }
private:
    spinlock_t lock_;
};

class LockGuard {
public:
    explicit LockGuard(SpinLock& l) : lock_(l) { lock_.lock(); }
    ~LockGuard() { lock_.unlock(); }
    LockGuard(const LockGuard&) = delete;
    LockGuard& operator=(const LockGuard&) = delete;
private:
    SpinLock& lock_;
};

template<typename Func>
inline auto with_lock(SpinLock& l, Func&& f) -> decltype(f())
{
    LockGuard g(l);
    return std::forward<Func>(f)();
}

#endif // SPINLOCK_HPP
