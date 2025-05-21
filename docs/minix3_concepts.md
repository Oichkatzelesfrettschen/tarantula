# MINIX 3 Concepts for the Microkernel Plan

The MINIX 3 operating system is known for running most device drivers and system
services outside the kernel. Three key ideas are relevant when adapting its
techniques to the BSD microkernel effort:

## User-space drivers
- Device drivers are regular processes that communicate with the kernel through
  well-defined APIs.
- Driver crashes do not bring down the kernel; failing processes can be
  restarted while the rest of the system continues running.

## Reincarnation Server
- A dedicated management service monitors all user-space drivers and servers.
- When a component stops responding, the Reincarnation Server automatically
  restarts it using a clean copy on disk.

## Interprocess communication (IPC)
- MINIX 3 relies on message-based IPC to coordinate between drivers, servers and
  user applications.
- Messages carry small, fixed-size structures and may be passed asynchronously or
  synchronously, depending on the service design.

## Adapting these ideas
The existing [microkernel plan](microkernel_plan.md) aims to move BSD device
drivers and subsystems out of the kernel. Borrowing from MINIX 3, future
milestones will:
1. Compile drivers as user-space programs that register with the microkernel.
2. Add a supervisory service, similar to the Reincarnation Server, to monitor and
   restart critical servers when they fail.
3. Define a lightweight message-passing API so drivers and system servers can
   exchange requests without relying on direct kernel calls.

These additions help isolate faults and simplify kernel responsibilities while
preserving compatibility with historical BSD sources.

