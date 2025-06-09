#pragma once
#ifndef LIBIPC_H
#define LIBIPC_H

#include <stdbool.h>
#include <stdint.h>

#include "exo_ipc.h"
#include "ipc.h"

/**\
 * @file libipc.h
 * @brief Lightweight helpers for IPC message exchange.
 */

/// Send message @p m via the kernel queue
static inline exo_ipc_status ipc_send(const struct ipc_message *m) {
    return ipc_queue_send_blocking(&kern_ipc_queue, m);
}

/// Receive a message and block until one is available
static inline exo_ipc_status ipc_recv(struct ipc_message *m) {
    return ipc_queue_recv_blocking(&kern_ipc_queue, m);
}

/// Attempt to receive with a bounded spin wait
static inline exo_ipc_status ipc_recv_t(struct ipc_message *m, unsigned tries) {
    return ipc_queue_recv_timed(&kern_ipc_queue, m, tries);
}

#endif /* LIBIPC_H */
