#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stdatomic.h>

typedef struct spinlock {
    atomic_flag flag;
} spinlock_t;

static inline void spinlock_init(spinlock_t *l)
{
    atomic_flag_clear(&l->flag);
}

static inline void spinlock_lock(spinlock_t *l)
{
    while (atomic_flag_test_and_set_explicit(&l->flag, memory_order_acquire))
        ;
}

static inline int spinlock_trylock(spinlock_t *l)
{
    return !atomic_flag_test_and_set_explicit(&l->flag, memory_order_acquire);
}

static inline void spinlock_unlock(spinlock_t *l)
{
    atomic_flag_clear_explicit(&l->flag, memory_order_release);
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
