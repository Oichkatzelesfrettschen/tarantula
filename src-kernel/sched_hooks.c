#include <stdio.h>
#include "../include/exokernel.h"
/* Stubs delegating to user-space scheduler */
extern void uland_sched_init(void);
void
kern_sched_init(void)
{
    uland_sched_init();
}
