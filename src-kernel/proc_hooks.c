#include <stdio.h>
#include "exokernel.h"
#include "ipc.h"
#include <unistd.h>
/* Stubs delegating to user-space process manager */
extern int pm_fork(void);
extern int pm_exec(const char *path, char *const argv[]);

int
kern_fork(void)
{

    struct ipc_mailbox *mb = ipc_get_mailbox();
    struct ipc_message msg = { .type = IPC_MSG_PROC_FORK };
    ipc_queue_send(mb, &msg);
    struct ipc_message reply;
    if (ipc_queue_recv(mb, &reply)) {
        if (reply.type != IPC_MSG_PROC_FORK)
            return (int)reply.a;
    }
    int pid = pm_fork();
    if (pid > 0)
        ipc_mailbox_alloc(pid);
    return pid;
}

int
kern_exec(const char *path, char *const argv[])
{
    struct ipc_message msg = {
        .type = IPC_MSG_PROC_EXEC,
        .a = (uintptr_t)path,
        .b = (uintptr_t)argv
    };
    struct ipc_mailbox *mb = ipc_get_mailbox();
    ipc_queue_send(mb, &msg);
    struct ipc_message reply;
    if (ipc_queue_recv(mb, &reply))
        return (int)reply.a;
    return pm_exec(path, argv);
}

