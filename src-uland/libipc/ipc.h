#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdint.h>
#include <stdbool.h>

#include "../../src-kernel/ipc.h"

/* User-space convenience wrappers */
static inline bool ipc_send(const struct ipc_message *m)
{
    return ipc_queue_send(&kern_ipc_queue, m);
}

static inline bool ipc_recv(struct ipc_message *m)
{
    return ipc_queue_recv(&kern_ipc_queue, m);
}

#endif /* LIBIPC_H */
