#ifndef SCHED_LOCK_H
#define SCHED_LOCK_H

#include "spinlock.h"

#ifdef __cplusplus
extern "C" {
#endif

SPINLOCK_DECLARE(sched_lock);

void sched_lock_acquire(void);
void sched_lock_release(void);

#ifdef __cplusplus
}
#endif

#endif /* SCHED_LOCK_H */
