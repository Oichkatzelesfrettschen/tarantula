#include <stdio.h>
#include "exokernel.h"
#include "ipc.h"
#include <unistd.h>
/* Stubs delegating to user-space file server */
extern int fs_open(const char *path, int flags);
int
kern_open(const char *path, int flags)
{
    struct ipc_message msg = {
        .type = IPC_MSG_OPEN,
        .a = (uintptr_t)path,
        .b = (uintptr_t)flags
    };
    struct ipc_mailbox *mb = ipc_get_mailbox();
    ipc_queue_send(mb, &msg);
    struct ipc_message reply;
    if (ipc_queue_recv(mb, &reply)) {
        if (reply.type != IPC_MSG_OPEN)
            return (int)reply.a;
    }
    return fs_open(path, flags);
}
