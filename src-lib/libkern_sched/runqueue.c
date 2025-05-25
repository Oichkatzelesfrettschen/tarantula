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

#include <sys/param.h>
#include <sys/proc.h>
#include <sys/resourcevar.h>
#include "runqueue.h"

/* Summary bitmask and actual run queue heads. */
int whichqs = 0;
struct prochd qs[NQS];

/*
 * Insert process p on the run queue indicated by its priority.
 * Calls should be made at splstatclock(), and p->p_stat should be SRUN.
 */
void
setrunqueue(struct proc *p)
{
    struct prochd *q;
    struct proc *oldlast;
    int which = p->p_priority >> 2;

    if (p->p_back != NULL)
        panic("setrunqueue");
    q = &qs[which];
    whichqs |= 1 << which;
    p->p_forw = (struct proc *)q;
    p->p_back = oldlast = q->ph_rlink;
    q->ph_rlink = p;
    oldlast->p_forw = p;
}

/*
 * Remove process p from its run queue, which should be the one
 * indicated by its priority.  Calls should be made at splstatclock().
 */
void
remrq(struct proc *p)
{
    int which = p->p_priority >> 2;
    struct prochd *q;

    if ((whichqs & (1 << which)) == 0)
        panic("remrq");
    p->p_forw->p_back = p->p_back;
    p->p_back->p_forw = p->p_forw;
    p->p_back = NULL;
    q = &qs[which];
    if (q->ph_link == (struct proc *)q)
        whichqs &= ~(1 << which);
}
