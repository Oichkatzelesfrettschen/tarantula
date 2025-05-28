#include "exokernel.h"

SPINLOCK_DEFINE(sched_lock);

void sched_lock_acquire(void) {}
void sched_lock_release(void) {}

_BitInt(32) runin = 0;
_BitInt(32) runout = 0;
void sched_increment_runin(void) { runin++; }
void sched_increment_runout(void) { runout++; }

void uland_sched_init(void) {}
