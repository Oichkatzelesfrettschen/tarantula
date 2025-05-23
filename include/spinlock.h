#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stdatomic.h>

typedef struct {
    atomic_flag flag;
} spinlock_t;

static inline void spinlock_init(spinlock_t *lock)
{
    atomic_flag_clear(&lock->flag);
}

static inline void spinlock_lock(spinlock_t *lock)
{
    while (atomic_flag_test_and_set_explicit(&lock->flag, memory_order_acquire))
        ;
}

static inline void spinlock_unlock(spinlock_t *lock)
{
    atomic_flag_clear_explicit(&lock->flag, memory_order_release);
}

#endif /* SPINLOCK_H */
