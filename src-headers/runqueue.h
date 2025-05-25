#pragma once
#ifndef RUNQUEUE_H
#define RUNQUEUE_H

#include <sys/proc.h>

/* Run queue heads and bitmask imported from the kernel scheduler. */
extern int whichqs;
extern struct prochd qs[NQS];

void setrunqueue(struct proc *p);
void remrq(struct proc *p);

#endif /* RUNQUEUE_H */
