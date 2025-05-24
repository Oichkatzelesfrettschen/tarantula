#ifndef EXOKERNEL_H
#define EXOKERNEL_H

/* Interface exported by the exokernel stubs. */

#include <stdbool.h>

void kern_sched_init(void);
int kern_open(const char *path, int flags);
bool kern_vm_fault(void *addr);
int kern_fork(void);
int kern_exec(const char *path, char *const argv[]);

#endif /* EXOKERNEL_H */
