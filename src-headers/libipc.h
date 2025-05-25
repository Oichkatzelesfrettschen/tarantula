#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdint.h>
#include <stdbool.h>

#include "ipc.h"

/* User-space convenience wrappers */
static inline ipc_status_t ipc_send(const struct ipc_message *m)
{
    return ipc_queue_send_blocking(&kern_ipc_queue, m);
}

static inline ipc_status_t ipc_recv(struct ipc_message *m)
{
    return ipc_queue_recv_blocking(&kern_ipc_queue, m);
}

#endif /* LIBIPC_H */
