#ifndef IPC_H
#define IPC_H

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include "spinlock.h"

#define IPC_QUEUE_SIZE 32

/* Message types used by kernel hooks */
enum ipc_msg_type {
    IPC_MSG_SCHED_INIT = 1,
    IPC_MSG_VM_FAULT,
    IPC_MSG_OPEN,
    IPC_MSG_PROC_FORK,
    IPC_MSG_PROC_EXEC,
    IPC_MSG_HEARTBEAT
};

struct ipc_message {
    uint32_t type;      /* enum ipc_msg_type */
    uintptr_t a;
    uintptr_t b;
    uintptr_t c;
};

struct ipc_queue {
    struct ipc_message msgs[IPC_QUEUE_SIZE];
    volatile uint32_t head;
    volatile uint32_t tail;
    spinlock_t lock;
};

/* Global queue instance defined in ipc.c */
extern struct ipc_queue kern_ipc_queue;

void ipc_queue_init(struct ipc_queue *q);
bool ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m);
bool ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m);
void ipc_queue_send_blocking(struct ipc_queue *q, const struct ipc_message *m);
void ipc_queue_recv_blocking(struct ipc_queue *q, struct ipc_message *m);

#endif /* IPC_H */
