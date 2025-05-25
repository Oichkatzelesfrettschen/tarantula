#include <stdio.h>
#include "exokernel.h"
#include "ipc.h"
#include <exo_ipc.h>
/* Stubs delegating to user-space process manager */
extern int pm_fork(void);
extern int pm_execve(const char *path, char *const argv[], char *const envp[]);
extern int pm_waitpid(int pid, int *status, int options);

int
kern_fork(void)
{

    struct ipc_message msg = { .type = IPC_MSG_PROC_FORK };
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb->queue, &reply, 1000) == EXO_IPC_OK) {
        if (reply.type != IPC_MSG_PROC_FORK)
            return (int)reply.a;
    }
    return pm_fork();
}

int
kern_execve(const char *path, char *const argv[], char *const envp[])
{
    struct ipc_message msg = {
        .type = IPC_MSG_PROC_EXEC,
        .a = (uintptr_t)path,
        .b = (uintptr_t)argv,
        .c = (uintptr_t)envp
    };
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb2 = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb2->queue, &reply, 1000) == EXO_IPC_OK)
        return (int)reply.a;
    return pm_execve(path, argv, envp);
}

int
kern_waitpid(int pid, int *status, int options)
{
    struct ipc_message msg = {
        .type = IPC_MSG_PROC_WAITPID,
        .a = (uintptr_t)pid,
        .b = (uintptr_t)status,
        .c = (uintptr_t)options
    };
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb->queue, &reply, 1000) == EXO_IPC_OK)
        return (int)reply.a;
    return pm_waitpid(pid, status, options);
}

