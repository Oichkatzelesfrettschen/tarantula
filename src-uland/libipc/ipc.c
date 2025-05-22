#include "ipc.h"

/* Shared queue used by kernel stubs and user-space servers */
struct ipc_queue kern_ipc_queue;

void ipc_queue_init(struct ipc_queue *q)
{
    q->head = q->tail = 0;
}

bool ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m)
{
    uint32_t next = (q->head + 1) % IPC_QUEUE_SIZE;
    if (next == q->tail)
        return false; /* full */
    q->msgs[q->head] = *m;
    q->head = next;
    return true;
}

bool ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m)
{
    if (q->tail == q->head)
        return false; /* empty */
    *m = q->msgs[q->tail];
    q->tail = (q->tail + 1) % IPC_QUEUE_SIZE;
    return true;
}
