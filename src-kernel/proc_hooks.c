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
    ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    if (ipc_queue_recv(&kern_ipc_queue, &reply)) {
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
    ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    if (ipc_queue_recv(&kern_ipc_queue, &reply))
        return (int)reply.a;
    return pm_exec(path, argv);
}

