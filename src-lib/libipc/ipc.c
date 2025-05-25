#include "ipc.h"
#include <exo_ipc.h>
#include <unistd.h>

/* Shared queue used by kernel stubs and user-space servers */
struct ipc_queue kern_ipc_queue;

#define IPC_MAX_MAILBOXES 32
static struct ipc_mailbox mailboxes[IPC_MAX_MAILBOXES];

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

exo_ipc_status ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m)
{
    exo_ipc_status status = EXO_IPC_FULL;
    lock_queue(q);
    uint32_t next = (q->head + 1) % IPC_QUEUE_SIZE;
    if (next != q->tail) {
        q->msgs[q->head] = *m;
        q->head = next;
        status = EXO_IPC_OK;
    }
    unlock_queue(q);
    return status;
}

exo_ipc_status ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m)
{
    exo_ipc_status status = EXO_IPC_EMPTY;
    lock_queue(q);
    if (q->tail != q->head) {
        *m = q->msgs[q->tail];
        q->tail = (q->tail + 1) % IPC_QUEUE_SIZE;
        status = EXO_IPC_OK;
    }
    unlock_queue(q);
    return status;
}

exo_ipc_status ipc_queue_send_blocking(struct ipc_queue *q, const struct ipc_message *m)
{
    exo_ipc_status st;
    while ((st = ipc_queue_send(q, m)) == EXO_IPC_FULL)
        ;
    return st;
}

exo_ipc_status ipc_queue_recv_blocking(struct ipc_queue *q, struct ipc_message *m)
{
    exo_ipc_status st;
    while ((st = ipc_queue_recv(q, m)) == EXO_IPC_EMPTY)
        ;
    return st;
}

exo_ipc_status ipc_queue_recv_timed(struct ipc_queue *q, struct ipc_message *m,
                                    unsigned tries)
{
    exo_ipc_status st;
    while (tries-- > 0) {
        st = ipc_queue_recv(q, m);
        if (st != EXO_IPC_EMPTY)
            return st;
        spin_pause();
    }
    return EXO_IPC_TIMEOUT;
}

void ipc_mailbox_init(void)
{
    for (int i = 0; i < IPC_MAX_MAILBOXES; ++i)
        mailboxes[i].pid = -1;
}

static struct ipc_mailbox *alloc_mailbox(int pid)
{
    for (int i = 0; i < IPC_MAX_MAILBOXES; ++i) {
        if (mailboxes[i].pid == -1) {
            mailboxes[i].pid = pid;
            ipc_queue_init(&mailboxes[i].queue);
            return &mailboxes[i];
        }
    }
    return NULL;
}

struct ipc_mailbox *ipc_mailbox_lookup(int pid)
{
    for (int i = 0; i < IPC_MAX_MAILBOXES; ++i) {
        if (mailboxes[i].pid == pid)
            return &mailboxes[i];
    }
    return alloc_mailbox(pid);
}

struct ipc_mailbox *ipc_mailbox_current(void)
{
    return ipc_mailbox_lookup(getpid());
}
