#pragma once
#ifndef RUNQUEUE_H
#define RUNQUEUE_H

#include <sys/proc.h>

/* Run queue management helpers */
void setrunqueue(struct proc *p);
void remrq(struct proc *p);

#endif /* RUNQUEUE_H */
