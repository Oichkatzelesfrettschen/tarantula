#include <stdio.h>
#include "exokernel.h"
#include "ipc.h"
/* Stubs delegating to user-space process manager */
extern int pm_fork(void);
extern int pm_exec(const char *path, char *const argv[]);

int
kern_fork(void)
{

    struct ipc_message msg = { .type = IPC_MSG_PROC_FORK };
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb->queue, &reply, 1000) == IPC_STATUS_SUCCESS) {
        if (reply.type != IPC_MSG_PROC_FORK)
            return (int)reply.a;
    }
    return pm_fork();
}

int
kern_exec(const char *path, char *const argv[])
{
    struct ipc_message msg = {
        .type = IPC_MSG_PROC_EXEC,
        .a = (uintptr_t)path,
        .b = (uintptr_t)argv
    };
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb2 = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb2->queue, &reply, 1000) == IPC_STATUS_SUCCESS)
        return (int)reply.a;
    return pm_exec(path, argv);
}

