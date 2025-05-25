/*
 * Shared run queue primitives extracted from per-arch locore.s files.
 * Originally implemented in assembly for each machine.
 * This version consolidates the logic in C so all kernels share
 * the same implementation.
 */
#include <sys/param.h>
#include <sys/proc.h>
#include <sys/resourcevar.h>

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
