#include "exokernel.h"

/*
 * Global counters tracking swap-in and swap-out events.
 * These variables mirror the historic runin/runout counters from
 * the 4.4BSD scheduler.  They provide statistics on how many
 * processes have been swapped into and out of memory.
 */
int runin = 0;
int runout = 0;

void
sched_increment_runin(void)
{
    sched_lock_acquire();
    runin++;
    sched_lock_release();
}

void
sched_increment_runout(void)
{
    sched_lock_acquire();
    runout++;
    sched_lock_release();
}

