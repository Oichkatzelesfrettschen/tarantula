#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdint.h>
#include <stdbool.h>

#include "ipc.h"

/* User-space convenience wrappers */
static inline bool ipc_send(const struct ipc_message *m)
{
    struct ipc_mailbox *mb = ipc_get_mailbox();
    if (!mb)
        return false;
    ipc_queue_send_blocking(mb, m);
    return true;
}

static inline bool ipc_recv(struct ipc_message *m)
{
    struct ipc_mailbox *mb = ipc_get_mailbox();
    if (!mb)
        return false;
    ipc_queue_recv_blocking(mb, m);
    return true;
}

#endif /* LIBIPC_H */
