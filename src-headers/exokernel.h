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
/* Use the C23 _BitInt type when available, otherwise fall back
 * to a standard 32-bit integer.  This keeps the headers compatible
 * with older compilers that may not yet implement _BitInt. */
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L
typedef _BitInt(32) run_counter_t;
#else
#include <stdint.h>
typedef int32_t run_counter_t;
#endif

extern run_counter_t runin;
extern run_counter_t runout;

void sched_increment_runin(void);
void sched_increment_runout(void);

void kern_sched_init(void);
int kern_open(const char *path, int flags);
bool kern_vm_fault(void *addr);
int kern_fork(void);
int kern_exec(const char *path, char *const argv[]);

#endif /* EXOKERNEL_H */
