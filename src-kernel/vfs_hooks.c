#include "exo_ipc.h"
#include "exokernel.h"
#include "ipc.h"
#include <stdio.h>
/* Stubs delegating to user-space file server */
extern int fs_open(const char *path, int flags);
/**
 * @brief Open a file via the user-space VFS server.
 *
 * Sends an IPC request to open @a path with the given @a flags. If the
 * call times out the builtin open stub is invoked.
 *
 * @param path Pathname of the file to open.
 * @param flags Flags passed to the open call.
 * @return File descriptor or negative error code.
 */
int kern_open(const char *path, int flags) {
    struct ipc_message msg = {
        .type = IPC_MSG_OPEN, .a = (uintptr_t)path, .b = (uintptr_t)flags};
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    struct ipc_mailbox *mb = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb->queue, &reply, 1000) == EXO_IPC_OK) {
        if (reply.type != IPC_MSG_OPEN)
            return (int)reply.a;
    }
    return fs_open(path, flags);
}
