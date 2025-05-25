#include "exokernel.h"
#include <sys/proc.h>
#include <sys/systm.h>

/* Global run queue state */
int whichqs;
struct prochd qs[NQS];

/*
 * Insert process into the run queue determined by its priority.
 */
void
setrunqueue(struct proc *p)
{
    struct prochd *q;
    struct proc *oldlast;
    int which = p->p_priority >> 2;

    sched_lock_acquire();

    if (p->p_back != NULL)
        panic("setrunqueue");

    q = &qs[which];
    whichqs |= 1 << which;
    p->p_forw = (struct proc *)q;
    p->p_back = oldlast = q->ph_rlink;
    q->ph_rlink = p;
    oldlast->p_forw = p;

    sched_lock_release();
}

/*
 * Remove process from its run queue.  Panic if bookkeeping disagrees.
 */
void
remrq(struct proc *p)
{
    int which = p->p_priority >> 2;
    struct prochd *q;

    sched_lock_acquire();

    if ((whichqs & (1 << which)) == 0)
        panic("remrq");

    p->p_forw->p_back = p->p_back;
    p->p_back->p_forw = p->p_forw;
    p->p_back = NULL;
    q = &qs[which];
    if (q->ph_link == (struct proc *)q)
        whichqs &= ~(1 << which);

    sched_lock_release();
}
