#include "exo_ipc.h"
#include "exokernel.h"
#include "ipc.h"
#include <stdio.h>
/* Stubs delegating to user-space process manager */
extern int pm_fork(void);
extern int pm_exec(const char *path, char *const argv[]);

/**
 * @brief Request the user-space process manager to fork.
 *
 * Sends an IPC message to the manager and waits for a reply. If no
 * response is received the local fallback implementation is used.
 *
 * @return child PID on success or a negative error code.
 */
int kern_fork(void) {

    struct ipc_message msg = {.type = IPC_MSG_PROC_FORK};
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb->queue, &reply, 1000) == EXO_IPC_OK) {
        if (reply.type == IPC_MSG_PROC_FORK)
            return (int)reply.a;
    }
    return pm_fork();
}

/**
 * @brief Execute a program via the process manager.
 *
 * @param path Path to the binary to run.
 * @param argv Argument vector for the new process.
 * @return 0 on success or a negative error code.
 */
int kern_exec(const char *path, char *const argv[]) {
    struct ipc_message msg = {
        .type = IPC_MSG_PROC_EXEC, .a = (uintptr_t)path, .b = (uintptr_t)argv};
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb2 = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb2->queue, &reply, 1000) == EXO_IPC_OK) {
        if (reply.type == IPC_MSG_PROC_EXEC)
            return (int)reply.a;
    }
    return pm_exec(path, argv);
}
