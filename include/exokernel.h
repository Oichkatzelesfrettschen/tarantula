#ifndef EXOKERNEL_H
#define EXOKERNEL_H

/* Interface exported by the exokernel stubs. */

void   kern_sched_init(void);
int    kern_open(const char *path, int flags);
int    kern_vm_fault(void *addr);

#endif /* EXOKERNEL_H */
