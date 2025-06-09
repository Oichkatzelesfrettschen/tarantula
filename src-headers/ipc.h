#pragma once
#ifndef IPC_H
#define IPC_H

#include "exo_ipc.h"
#include "spinlock.h"
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>

#define IPC_QUEUE_SIZE 32 ///< Number of messages per IPC queue

/// Message types used by kernel hooks
enum ipc_msg_type {
    IPC_MSG_SCHED_INIT = 1,
    IPC_MSG_VM_FAULT,
    IPC_MSG_OPEN,
    IPC_MSG_PROC_FORK,
    IPC_MSG_PROC_EXEC,
    IPC_MSG_HEARTBEAT
};

/// Encapsulates a single IPC message
struct ipc_message {
    uint32_t type; /* enum ipc_msg_type */
    uintptr_t a;
    uintptr_t b;
    uintptr_t c;
};

/// Lockless ring buffer for IPC messages
struct ipc_queue {
    struct ipc_message msgs[IPC_QUEUE_SIZE];
    volatile uint32_t head;
    volatile uint32_t tail;
    spinlock_t lock;
};

/** Global queue instance defined in ipc.c */
extern struct ipc_queue kern_ipc_queue;

/** Initialize @p q for message passing */
void ipc_queue_init(struct ipc_queue *q);
/** Enqueue @p m onto @p q */
exo_ipc_status ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m);
/** Dequeue a message from @p q */
exo_ipc_status ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m);
/** Send, waiting if the queue is full */
exo_ipc_status ipc_queue_send_blocking(struct ipc_queue *q,
                                       const struct ipc_message *m);
/** Receive, blocking until a message is available */
exo_ipc_status ipc_queue_recv_blocking(struct ipc_queue *q,
                                       struct ipc_message *m);
/**
 * Receive from @p q with timeout.
 * @param tries Number of polls before timing out.
 */
exo_ipc_status ipc_queue_recv_timed(struct ipc_queue *q, struct ipc_message *m,
                                    unsigned tries);

/// Basic per-process mailbox
struct ipc_mailbox {
    int pid;
    struct ipc_queue queue;
};

/** Initialize the mailbox table */
void ipc_mailbox_init(void);
/** Locate mailbox for @p pid or create one */
struct ipc_mailbox *ipc_mailbox_lookup(int pid);
/** Return the mailbox for the current process */
struct ipc_mailbox *ipc_mailbox_current(void);

#endif /* IPC_H */
