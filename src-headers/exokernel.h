#pragma once
#ifndef EXOKERNEL_H
#define EXOKERNEL_H

/* Interface exported by the exokernel stubs. */

#include <stdbool.h>
#include "spinlock.h"

SPINLOCK_DECLARE(sched_lock);
void sched_lock_acquire(void);
void sched_lock_release(void);

/*
 * Counters tracking the number of processes swapped in and out.
 * Derived from historic BSD scheduler variables.
 */
extern int runin;
extern int runout;

void sched_increment_runin(void);
void sched_increment_runout(void);

void kern_sched_init(void);
int kern_open(const char *path, int flags);
bool kern_vm_fault(void *addr);
int kern_fork(void);
int kern_execve(const char *path, char *const argv[], char *const envp[]);
int kern_waitpid(int pid, int *status, int options);

#endif /* EXOKERNEL_H */
