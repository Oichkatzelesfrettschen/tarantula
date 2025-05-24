#include <stdio.h>
#include "exokernel.h"
#include "ipc.h"
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
    ipc_queue_send(&kern_ipc_queue, &msg);
    struct ipc_message reply;
    if (ipc_queue_recv(&kern_ipc_queue, &reply))
        return (int)reply.a;
    return fs_open(path, flags);
}
