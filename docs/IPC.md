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

Queue operations return one of four status values:

- `IPC_STATUS_SUCCESS` – the operation completed successfully.
- `IPC_STATUS_EMPTY` – a receive operation found no messages.
- `IPC_STATUS_FULL` – a send operation found the queue full.
- `IPC_STATUS_TIMEOUT` – a timed receive exceeded the retry budget.

## Send and Receive Semantics

Two non‑blocking helpers operate on a queue and return an `ipc_status_t`
value describing the outcome:

- `ipc_status_t ipc_queue_send(struct ipc_queue *q, const struct ipc_message *m)`
  – attempts to enqueue `m` and returns `IPC_STATUS_SUCCESS`,
  `IPC_STATUS_FULL` or `IPC_STATUS_TIMEOUT`.
- `ipc_status_t ipc_queue_recv(struct ipc_queue *q, struct ipc_message *m)` –
  attempts to dequeue the next message and returns `IPC_STATUS_SUCCESS` or
  `IPC_STATUS_EMPTY`.

Blocking variants `ipc_queue_send_blocking()` and
`ipc_queue_recv_blocking()` repeatedly call the non‑blocking forms until
they succeed.  The wrappers `ipc_send()` and `ipc_recv()` in
`libipc.h` invoke these blocking functions and report the resulting
status. A convenience wrapper `ipc_recv_t()` polls with a limited
retry count before returning `IPC_STATUS_TIMEOUT`.

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
