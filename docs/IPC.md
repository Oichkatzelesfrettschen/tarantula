# Interprocess Communication API

This document describes the lightweight mailbox mechanism used by the
microkernel stubs and user–space servers.  The API lives in
`src-headers/ipc.h` and is implemented by `src-lib/libipc/ipc.c`.

## Mailbox Creation

A mailbox is represented by `struct ipc_queue`.  The queue stores a fixed
number (`IPC_QUEUE_SIZE`, currently 32) of `struct ipc_message` entries in
a ring buffer protected by a spinlock.  To create a new mailbox simply
allocate a queue object and call:

```c
struct ipc_queue q;
ipc_queue_init(&q);
```

The global queue `kern_ipc_queue` is used by the kernel hooks and user
servers, but additional queues may be defined by applications.

## Messages

Each message contains a type identifier and three word-sized arguments:

```c
struct ipc_message {
    uint32_t type;      /* enum ipc_msg_type */
    uintptr_t a;
    uintptr_t b;
    uintptr_t c;
};
```

The exact meaning of the fields depends on the message type.  Producers
write a populated structure into the queue and consumers read it back.

### Status Codes

Queue operations return an `exo_ipc_status` value:

- `EXO_IPC_OK` – the operation completed successfully.
- `EXO_IPC_EMPTY` – a receive operation found no messages.
- `EXO_IPC_FULL` – a send operation found the queue full.
- `EXO_IPC_TIMEOUT` – a timed receive exceeded the retry budget.
- `EXO_IPC_ERROR` – an unspecified failure occurred.

## Send and Receive Semantics

Two non‑blocking helpers operate on a queue and return an `exo_ipc_status`
value describing the outcome:

- `exo_ipc_status ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m)`
  – attempts to enqueue `m` and returns `EXO_IPC_OK`,
  `EXO_IPC_FULL` or `EXO_IPC_TIMEOUT`.
- `exo_ipc_status ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m)` –
  attempts to dequeue the next message and returns `EXO_IPC_OK` or
  `EXO_IPC_EMPTY`.

Blocking variants `ipc_queue_send_blocking()` and
`ipc_queue_recv_blocking()` repeatedly call the non‑blocking forms until
they succeed.  The wrappers `ipc_send()` and `ipc_recv()` in
`libipc.h` invoke these blocking functions and report the resulting
status. A convenience wrapper `ipc_recv_t()` polls with a limited
retry count before returning `EXO_IPC_TIMEOUT`.

## Timeout Behavior

The blocking helpers spin until the operation completes and do not
provide a timeout.  Callers that need a timeout should poll using the
non‑blocking functions and abort after an application‑defined period.
For example:

```c
struct ipc_message m = { .type = IPC_MSG_HEARTBEAT };
unsigned tries = 0;
while (!ipc_queue_send(&q, &m)) {
    if (++tries > MAX_TRIES)
        return false; /* timed out */
    spin_pause();
}
return true;
```

A future enhancement may add optional timeout parameters to the blocking
routines, but the current API relies on explicit polling when timing out
is required.

## Cap'n Proto Stub

When the build is invoked with `CAPNP=1` a minimal `libcapnp` library is
compiled under `third_party/libcapnp`.  The stub currently implements only a
single helper:

```c
int capnp_parse(const char *buf, size_t len, struct capnp_message *msg);
```

The `tools/memserver` program links against this stub.  It loads a file into
memory and prints the parsed message size.  A basic regression test lives under
`tests/modern` and is built automatically when `CAPNP=1` is supplied to `make`.

## POSIX IPC Wrappers

`libipc` also provides lightweight wrappers around the standard POSIX
message queue, semaphore and shared memory APIs.  The functions accept a
directory file descriptor as their first argument to support future
capability-based restrictions.  The current implementation simply calls
the regular POSIX routines.

```c
mqd_t cap_mq_open(int dirfd, const char *name, int oflag, mode_t mode,
                  struct mq_attr *attr);
int   cap_mq_unlink(int dirfd, const char *name);

sem_t *cap_sem_open(int dirfd, const char *name, int oflag, mode_t mode,
                    unsigned value);
int   cap_sem_unlink(int dirfd, const char *name);

int cap_shm_open(int dirfd, const char *name, int oflag, mode_t mode);
int cap_shm_unlink(int dirfd, const char *name);
```

The program `tests/modern/posix_ipc_demo.c` demonstrates basic usage of
these helpers.
