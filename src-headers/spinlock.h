#pragma once
#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>


#ifndef SPINLOCK_CACHELINE
# define SPINLOCK_CACHELINE 64
#endif

#define SPINLOCK_INITIALIZER { false }

#if defined(__x86_64__) || defined(__i386__)
# define spin_pause() __builtin_ia32_pause()
static inline unsigned spinlock_cacheline_size(void)
{
    unsigned eax, ebx, ecx, edx;
    __asm__ volatile("cpuid"
                     : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
                     : "a"(1), "c"(0));
    unsigned cl = ((ebx >> 8) & 0xff) * 8;
    return cl ? cl : SPINLOCK_CACHELINE;
}
#else
# define spin_pause() ((void)0)
static inline unsigned spinlock_cacheline_size(void)
{
    return SPINLOCK_CACHELINE;
}
#endif

typedef struct spinlock {
    atomic_bool locked;
} spinlock_t __attribute__((aligned(SPINLOCK_CACHELINE)));

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

/*
 * Optional ticket lock ensuring FIFO fairness. Not used by default
 * but provided for components with heavy contention.
 */
typedef struct ticketlock {
    atomic_uint next;
    atomic_uint owner;
} ticketlock_t __attribute__((aligned(SPINLOCK_CACHELINE)));

#define TICKETLOCK_INITIALIZER { 0, 0 }

#define TICKETLOCK_DEFINE(name) \
    ticketlock_t name = TICKETLOCK_INITIALIZER
#define TICKETLOCK_DECLARE(name) \
    extern ticketlock_t name

static inline void ticketlock_init(ticketlock_t *l)
{
    atomic_init(&l->next, 0);
    atomic_init(&l->owner, 0);
}

static inline void ticketlock_lock(ticketlock_t *l)
{
    unsigned ticket = atomic_fetch_add_explicit(&l->next, 1, memory_order_relaxed);
    while (atomic_load_explicit(&l->owner, memory_order_acquire) != ticket)
        spin_pause();
}

static inline int ticketlock_trylock(ticketlock_t *l)
{
    unsigned owner = atomic_load_explicit(&l->owner, memory_order_relaxed);
    unsigned next = atomic_load_explicit(&l->next, memory_order_relaxed);
    if (owner == next &&
        atomic_compare_exchange_strong_explicit(&l->next, &next, next + 1,
                                               memory_order_acquire,
                                               memory_order_relaxed)) {
        return 1;
    }
    return 0;
}

static inline void ticketlock_unlock(ticketlock_t *l)
{
    atomic_fetch_add_explicit(&l->owner, 1, memory_order_release);
}

static inline void spinlock_guard_release(spinlock_guard_t *g)
{
    if (g->lock)
        spinlock_unlock(g->lock);
}

#define SCOPED_SPINLOCK(name, lockptr) \
    spinlock_guard_t name __attribute__((cleanup(spinlock_guard_release))) = { .lock = (lockptr) }; \
    spinlock_lock(name.lock)

#ifndef CONFIG_SMP
# define CONFIG_SMP 1
#endif

#if CONFIG_SMP
# define spin_lock(l)   spinlock_lock(l)
# define spin_unlock(l) spinlock_unlock(l)
# define spin_trylock(l) spinlock_trylock(l)
#else
# define spin_lock(l)   ((void)0)
# define spin_unlock(l) ((void)0)
# define spin_trylock(l) (1)
#endif

#endif /* SPINLOCK_H */
