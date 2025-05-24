#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stdatomic.h>
#include <stdbool.h>

#define SPINLOCK_INITIALIZER { false }

#if defined(__x86_64__) || defined(__i386__)
# define spin_pause() __builtin_ia32_pause()
#else
# define spin_pause() ((void)0)
#endif

typedef struct spinlock {
    atomic_bool locked;
} spinlock_t;

#define SPINLOCK_DEFINE(name) \
    spinlock_t name = SPINLOCK_INITIALIZER
#define SPINLOCK_DECLARE(name) \
    extern spinlock_t name

static inline void spinlock_init(spinlock_t *l)
{
    atomic_store_explicit(&l->locked, false, memory_order_relaxed);
}

static inline bool spinlock_is_locked(const spinlock_t *l)
{
    return atomic_load_explicit(&l->locked, memory_order_relaxed);
}

static inline void spinlock_lock(spinlock_t *l)
{
    bool expected = false;
    while (!atomic_compare_exchange_weak_explicit(&l->locked, &expected, true,
                                                 memory_order_acquire,
                                                 memory_order_relaxed)) {
        expected = false;
        spin_pause();
    }
}

static inline int spinlock_trylock(spinlock_t *l)
{
    bool expected = false;
    return atomic_compare_exchange_strong_explicit(&l->locked, &expected, true,
                                                   memory_order_acquire,
                                                   memory_order_relaxed);
}

static inline void spinlock_unlock(spinlock_t *l)
{
    atomic_store_explicit(&l->locked, false, memory_order_release);
}

typedef struct spinlock_guard {
    spinlock_t *lock;
} spinlock_guard_t;

static inline void spinlock_guard_release(spinlock_guard_t *g)
{
    if (g->lock)
        spinlock_unlock(g->lock);
}

#define SCOPED_SPINLOCK(name, lockptr) \
    spinlock_guard_t name __attribute__((cleanup(spinlock_guard_release))) = { .lock = (lockptr) }; \
    spinlock_lock(name.lock)

#endif /* SPINLOCK_H */
