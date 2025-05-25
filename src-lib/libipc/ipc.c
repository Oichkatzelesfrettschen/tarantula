#include "ipc.h"
#include <unistd.h>

/* Mailboxes shared between kernel stubs and user-space servers */
struct ipc_mailbox ipc_mailboxes[IPC_MAX_MAILBOXES];

static struct ipc_mailbox *lookup(int pid)
{
    if (pid < 0 || pid >= IPC_MAX_MAILBOXES)
        return NULL;
    if (!atomic_load_explicit(&ipc_mailboxes[pid].active, memory_order_acquire))
        return NULL;
    return &ipc_mailboxes[pid];
}

struct ipc_mailbox *ipc_mailbox_lookup(int pid)
{
    return lookup(pid);
}

struct ipc_mailbox *ipc_get_mailbox(void)
{
    return lookup(getpid());
}

void ipc_mailbox_alloc(int pid)
{
    if (pid < 0 || pid >= IPC_MAX_MAILBOXES)
        return;
    ipc_queue_init(&ipc_mailboxes[pid]);
}

void ipc_mailbox_free(int pid)
{
    if (pid < 0 || pid >= IPC_MAX_MAILBOXES)
        return;
    atomic_store_explicit(&ipc_mailboxes[pid].active, false, memory_order_release);
}

static void lock_queue(struct ipc_queue *q)
{
    spinlock_lock(&q->lock);
}

static void unlock_queue(struct ipc_queue *q)
{
    spinlock_unlock(&q->lock);
}

void ipc_queue_init(struct ipc_mailbox *mb)
{
    struct ipc_queue *q = &mb->q;
    q->head = q->tail = 0;
    spinlock_init(&q->lock);
    mb->pid = getpid();
    atomic_store_explicit(&mb->active, true, memory_order_release);
}

bool ipc_queue_send(struct ipc_mailbox *mb, const struct ipc_message *m)
{
    bool ok = false;
    struct ipc_queue *q = &mb->q;
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

bool ipc_queue_recv(struct ipc_mailbox *mb, struct ipc_message *m)
{
    bool ok = false;
    struct ipc_queue *q = &mb->q;
    lock_queue(q);
    if (q->tail != q->head) {
        *m = q->msgs[q->tail];
        q->tail = (q->tail + 1) % IPC_QUEUE_SIZE;
        ok = true;
    }
    unlock_queue(q);
    return ok;
}

void ipc_queue_send_blocking(struct ipc_mailbox *mb, const struct ipc_message *m)
{
    while (!ipc_queue_send(mb, m))
        ;
}

void ipc_queue_recv_blocking(struct ipc_mailbox *mb, struct ipc_message *m)
{
    while (!ipc_queue_recv(mb, m))
        ;
}
