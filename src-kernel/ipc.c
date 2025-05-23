#include "ipc.h"
#include "spinlock.h"

/* Shared queue used by kernel stubs and user-space servers */
struct ipc_queue kern_ipc_queue;

static void lock_queue(struct ipc_queue *q)
{
    spinlock_lock(&q->lock);
}

static void unlock_queue(struct ipc_queue *q)
{
    spinlock_unlock(&q->lock);
}

void ipc_queue_init(struct ipc_queue *q)
{
    q->head = q->tail = 0;
    spinlock_init(&q->lock);
}

bool ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m)
{
    bool ok = false;
    lock_queue(q);
    uint32_t next = (q->head + 1) % IPC_QUEUE_SIZE;
    if (next != q->tail) {
        q->msgs[q->head] = *m;
        q->head = next;
        ok = true;
    }
    unlock_queue(q);
    return ok;
}

bool ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m)
{
    bool ok = false;
    lock_queue(q);
    if (q->tail != q->head) {
        *m = q->msgs[q->tail];
        q->tail = (q->tail + 1) % IPC_QUEUE_SIZE;
        ok = true;
    }
    unlock_queue(q);
    return ok;
}

void ipc_queue_send_blocking(struct ipc_queue *q, const struct ipc_message *m)
{
    while (!ipc_queue_send(q, m))
        ;
}

void ipc_queue_recv_blocking(struct ipc_queue *q, struct ipc_message *m)
{
    while (!ipc_queue_recv(q, m))
        ;
}
