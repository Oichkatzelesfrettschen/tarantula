#pragma once
#ifndef MAILBOX_T_H
#define MAILBOX_T_H

#include "ipc.h"
#include <stddef.h>
#include <time.h>

static inline ipc_status_t ipc_recv_t(struct ipc_mailbox **boxes, size_t count,
                                      struct ipc_message *m, unsigned tries,
                                      const struct timespec *ts)
{
    return mailbox_recv_t(boxes, count, m, tries, ts);
}

#endif /* MAILBOX_T_H */
