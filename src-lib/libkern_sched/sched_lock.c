#include "sched_lock.h"

SPINLOCK_DEFINE(sched_lock);

void sched_lock_acquire(void)
{
    spin_lock(&sched_lock);
}

void sched_lock_release(void)
{
    spin_unlock(&sched_lock);
}
