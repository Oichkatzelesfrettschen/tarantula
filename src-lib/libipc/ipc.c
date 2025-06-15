#include "ipc.h"
#include "exo_ipc.h"
#include <unistd.h>
#include <sched.h>

/** Shared queue used by kernel stubs and user-space servers. */
struct ipc_queue kern_ipc_queue;

#define IPC_MAX_MAILBOXES 32
static struct ipc_mailbox mailboxes[IPC_MAX_MAILBOXES];

/*
 * Small circular buffer logging the most recent IPC messages. The queue
 * is used for debugging failed timed receives and is intentionally
 * separate from the public ipc_mailbox API.
 */
#define MAILBOX_BUFSZ 16
struct mailbox {
    struct ipc_message buf[MAILBOX_BUFSZ];
    uint32_t head;
};

static struct mailbox ipcs;

static void lock_queue(struct ipc_queue *q) { spinlock_lock(&q->lock); }

static void unlock_queue(struct ipc_queue *q) { spinlock_unlock(&q->lock); }

/**
 * @brief Initialize an IPC queue.
 *
 * Sets the head and tail pointers to zero and initializes the
 * internal spinlock.
 *
 * @param q Queue to initialize.
 */
void ipc_queue_init(struct ipc_queue *q) {
    q->head = q->tail = 0;
    spinlock_init(&q->lock);
}

/**
 * @brief Send an IPC message.
 *
 * Adds the message @a m to the queue if space permits.
 *
 * @param q Target queue.
 * @param m Message to enqueue.
 * @return Status code indicating success or queue full.
 */

exo_ipc_status ipc_queue_send(struct ipc_queue *q,
                              const struct ipc_message *m) {
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

/**
 * @brief Receive an IPC message from a queue.
 *
 * @param q Queue to dequeue from.
 * @param m Output pointer for the received message.
 * @return Status code indicating success or queue empty.
 */
exo_ipc_status ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m) {
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

/**
 * @brief Send a message, spinning until space is available.
 */
exo_ipc_status ipc_queue_send_blocking(struct ipc_queue *q,
                                       const struct ipc_message *m) {
    exo_ipc_status st;
    while ((st = ipc_queue_send(q, m)) == EXO_IPC_FULL)
        ;
    return st;
}

/**
 * @brief Send a message and yield the CPU.
 *
 * The caller yields after enqueueing to allow the receiver to run
 * immediately, enabling low-latency RPC patterns.
 */
exo_ipc_status ipc_queue_send_yield(struct ipc_queue *q,
                                    const struct ipc_message *m) {
    exo_ipc_status st = ipc_queue_send(q, m);
    sched_yield();
    return st;
}

/**
 * @brief Receive a message, blocking until one is queued.
 */
exo_ipc_status ipc_queue_recv_blocking(struct ipc_queue *q,
                                       struct ipc_message *m) {
    exo_ipc_status st;
    while ((st = ipc_queue_recv(q, m)) == EXO_IPC_EMPTY)
        ;
    return st;
}

/**
 * @brief Receive with a limited number of polling attempts.
 */
exo_ipc_status ipc_queue_recv_timed(struct ipc_queue *q, struct ipc_message *m,
                                    unsigned tries) {
    static int init_done;
    if (!init_done) {
        ipcs.head = 0;
        init_done = 1;
    }
    exo_ipc_status st;
    while (tries-- > 0) {
        st = ipc_queue_recv(q, m);
        if (st != EXO_IPC_EMPTY) {
            ipcs.buf[ipcs.head] = *m;
            ipcs.head = (ipcs.head + 1) % MAILBOX_BUFSZ;
            return st;
        }
        spin_pause();
    }
    return EXO_IPC_TIMEOUT;
}

/**
 * @brief Initialize mailbox table used by IPC.
 */
void ipc_mailbox_init(void) {
    for (int i = 0; i < IPC_MAX_MAILBOXES; ++i)
        mailboxes[i].pid = -1;
}

/** Allocate a new mailbox entry for @p pid if space permits. */
static struct ipc_mailbox *alloc_mailbox(int pid) {
    for (int i = 0; i < IPC_MAX_MAILBOXES; ++i) {
        if (mailboxes[i].pid == -1) {
            mailboxes[i].pid = pid;
            ipc_queue_init(&mailboxes[i].queue);
            return &mailboxes[i];
        }
    }
    return NULL;
}

/** Lookup an existing mailbox for @p pid or allocate one */
struct ipc_mailbox *ipc_mailbox_lookup(int pid) {
    for (int i = 0; i < IPC_MAX_MAILBOXES; ++i) {
        if (mailboxes[i].pid == pid)
            return &mailboxes[i];
    }
    return alloc_mailbox(pid);
}

/** Shortcut for the current process mailbox */
struct ipc_mailbox *ipc_mailbox_current(void) {
    return ipc_mailbox_lookup(getpid());
}

#include "posix_ipc.h"
#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <sys/mman.h>

/** Capability-friendly wrapper around mq_open */
mqd_t cap_mq_open(int dirfd, const char *name, int oflag, mode_t mode,
                  struct mq_attr *attr) {
    (void)dirfd;
    return mq_open(name, oflag, mode, attr);
}

/** Wrapper around mq_unlink */
int cap_mq_unlink(int dirfd, const char *name) {
    (void)dirfd;
    return mq_unlink(name);
}

/** Wrapper around sem_open */
sem_t *cap_sem_open(int dirfd, const char *name, int oflag, mode_t mode,
                    unsigned value) {
    (void)dirfd;
    return sem_open(name, oflag, mode, value);
}

/** Wrapper around sem_unlink */
int cap_sem_unlink(int dirfd, const char *name) {
    (void)dirfd;
    return sem_unlink(name);
}

/** Wrapper around shm_open */
int cap_shm_open(int dirfd, const char *name, int oflag, mode_t mode) {
    (void)dirfd;
    return shm_open(name, oflag, mode);
}

/** Wrapper around shm_unlink */
int cap_shm_unlink(int dirfd, const char *name) {
    (void)dirfd;
    return shm_unlink(name);
}
