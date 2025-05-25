#pragma once
#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdint.h>
#include <stdbool.h>

#include "ipc.h"
#include <exo_ipc.h>

/* User-space convenience wrappers */
static inline exo_ipc_status ipc_send(const struct ipc_message *m)
{
    return ipc_queue_send_blocking(&kern_ipc_queue, m);
}

static inline exo_ipc_status ipc_recv(struct ipc_message *m)
{
    return ipc_queue_recv_blocking(&kern_ipc_queue, m);
}

static inline exo_ipc_status ipc_recv_t(struct ipc_message *m, unsigned tries)
{
    return ipc_queue_recv_timed(&kern_ipc_queue, m, tries);
}

#endif /* LIBIPC_H */
