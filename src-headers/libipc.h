#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdint.h>
#include <stdbool.h>

#include "ipc.h"

/* User-space convenience wrappers */
static inline bool ipc_send(const struct ipc_message *m)
{
    ipc_queue_send_blocking(&kern_ipc_queue, m);
    return true;
}

static inline bool ipc_recv(struct ipc_message *m)
{
    ipc_queue_recv_blocking(&kern_ipc_queue, m);
    return true;
}

static inline enum ipc_recv_status ipc_recv_timeout(struct ipc_message *m,
                                                    uint32_t timeout_ms)
{
    return ipc_queue_recv_timeout(&kern_ipc_queue, m, timeout_ms);
}

#endif /* LIBIPC_H */
