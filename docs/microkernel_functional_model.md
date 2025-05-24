# Microkernel Functional Model

This document summarizes how the evolving microkernel and its user-space
components interact.  It complements `microkernel_plan.md` by describing
expected responsibilities and message flows.

## Core Microkernel Responsibilities

The microkernel contains only the minimal mechanisms needed to run the
system safely.  These include:

- **Thread scheduling hooks** – the kernel delegates policy decisions to the
  user-space scheduler library.  It starts execution in `kern_sched_init()`
  which initializes the global IPC queue before any messages are sent and
  then performs context switches on request.
- **Virtual memory hooks** – page faults call `kern_vm_fault()` which forwards
  to a user-space memory manager for allocation and paging decisions.
- **System call gate** – simple wrappers like `kern_open()` pass file
  operations to the file server running in user space.
- **IPC primitives** – the kernel exposes message queues for servers and
  drivers to communicate.  Messages are fixed-size structures shared via a ring buffer.
### Memory Reservation and OOM Policy

The kernel invokes the OOM policy whenever a page allocation fails or free memory drops below its reserved threshold. The routine uses an emergency pool so it can post a low-memory message on the IPC queue.

User-space memory managers listening on that queue should reclaim caches and page out unused data when notified. If pressure continues, they may terminate the least important tasks and then report success back to the kernel.

The microkernel itself remains small and largely architecture independent.
Device drivers, filesystems and process management are all provided by
servers outside the kernel.

## User-space Servers

User-space components implement nearly all traditional BSD services:

- The **process manager** handles fork, exec and signal delivery.  It runs as
  `proc_manager` in `src-uland/servers`.
- The **file server** (`fs_server`) maintains vnodes and dispatches file
  requests from the `kern_open()` hook.
- The **scheduler library** and **VM library** in `src-uland/libkern_sched`
  and `src-uland/libvm` make policy decisions for scheduling and memory
  management.
- Capability management uses `cap_set_security_mode(cap_endpoint, mode)` to
  toggle security levels (`FAST`, `HARDENED` or `PARANOID`) for a running
  service.
- Additional drivers will appear under `src-uland/servers` as standalone
  tasks communicating with the kernel via the IPC layer.

Each server starts at boot time via init scripts and registers with the
microkernel.  Crashes can be detected by a simple watchdog process so that
failed components are restarted automatically.

## Message Flow Example

1. A user program calls `open("/etc/passwd", O_RDONLY)`.
2. The kernel trap handler invokes `kern_open()`.
3. `kern_open()` packages the request into an IPC message and sends it to
   the file server.
4. The file server translates the path, checks permissions and returns a file
   descriptor.
5. The kernel relays this descriptor back to the user program.

Other operations follow the same pattern: the kernel validates basic
parameters, packages the request and relies on a user-space server to
perform the real work.  This separation keeps the kernel small and easier
to reason about.


### IPC Usage Example

The ring-buffer API exposes three helper functions:

```c
struct ipc_queue q;
ipc_queue_init(&q);

struct ipc_message m = { .type = IPC_MSG_OPEN,
                         .a = (uintptr_t)"/etc/passwd",
                         .b = O_RDONLY };
ipc_queue_send(&q, &m);
if (ipc_queue_recv(&q, &m)) {
    int fd = (int)m.a;
    /* use fd */
}
```

Kernel hooks such as `kern_open()` push a request message to the queue and wait
for a corresponding reply from the user-space server.

The queue implementation originally offered only non-blocking `ipc_queue_send()`
and `ipc_queue_recv()` calls.  To simplify users of the API a lightweight
the ring buffer is protected by a small spinlock implemented in
`include/spinlock.h`. Two blocking helpers were added:
`ipc_queue_send_blocking()` and `ipc_queue_recv_blocking()`.  These functions
busy-wait until the operation completes.  User-space wrappers `ipc_send()` and
`ipc_recv()` invoke the blocking variants to guarantee delivery.
