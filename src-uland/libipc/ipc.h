#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdint.h>
#include <stdbool.h>

#include <ipc.h>

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

#endif /* LIBIPC_H */
