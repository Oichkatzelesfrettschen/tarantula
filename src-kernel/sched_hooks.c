#include <stdio.h>
#include "../include/exokernel.h"
#include "ipc.h"
/* Stubs delegating to user-space scheduler */
extern void uland_sched_init(void);
void
kern_sched_init(void)
{
    /* Ensure the message queue is ready before sending */
    ipc_queue_init(&kern_ipc_queue);

    struct ipc_message msg = { .type = IPC_MSG_SCHED_INIT };
    ipc_queue_send(&kern_ipc_queue, &msg);
    /* For now also directly call user library */
    uland_sched_init();
}
