#include <stdio.h>
#include "exokernel.h"
#include "ipc.h"
#include <unistd.h>
/* Stubs delegating to user-space scheduler */
extern void uland_sched_init(void);
void
kern_sched_init(void)
{
    ipc_mailbox_alloc(getpid());
    struct ipc_mailbox *mb = ipc_get_mailbox();
    struct ipc_message msg = { .type = IPC_MSG_SCHED_INIT };
    ipc_queue_send(mb, &msg);
    /* For now also directly call user library */
    uland_sched_init();
}
