# Hybrid Kernel Stubs Plan

This document outlines how the lightweight stub files under `src-kernel/` work alongside the legacy `sys/` kernel sources.  It also summarizes which subsystems continue to build into the monolithic kernel and which ones run in user space.  The details here complement the broader roadmaps in [microkernel_plan.md](microkernel_plan.md) and [exokernel_plan.md](exokernel_plan.md).

## Interaction with the Legacy Kernel

The files `proc_hooks.c`, `sched_hooks.c`, `vm_hooks.c` and `vfs_hooks.c` compile into `libkern_stubs.a`.  When linked with the historical kernel tree they override the default system call handlers:

- Each stub packages the original request into an IPC message using the queue defined in `src-headers/ipc.h`.
- The message is sent to a user-space manager (process manager, scheduler, VM library or file server).
- If the user-space side replies, the stub returns that result.  Should the reply fail, it falls back to the legacy routine still present under `sys/`.

This approach lets the modern components evolve without fully removing the old code.  The original implementations in `sys/` remain available so the system can boot even when user-space servers are missing.

## Subsystem Placement

Only a small core stays in the kernel:

- The memory allocator and low‐level interrupt handlers from `sys/kern` continue to link directly into the kernel image.
- Basic device support used during early boot (console and disk I/O) is still built from the historical sources.

Everything else is intended to run in user space or through the stub layer:

- Process management, scheduling and the virtual memory policy live in managers built under `src-uland/`.
- File system services and network protocols also move to user-space servers.
- Additional drivers are compiled as separate tasks that communicate with the kernel using the same IPC scheme.

The [microkernel plan](microkernel_plan.md) describes the steps to extract these services.  The [exokernel plan](exokernel_plan.md) pushes the idea further by stripping nearly all policy out of the kernel.

## Goals of the Hybrid Model

By keeping the legacy `sys/` tree intact we maintain historical context and a working baseline.  The stubs provide a clear integration point so subsystems can be moved gradually.  As more managers mature in user space the fallback paths in the stubs will become unnecessary, leaving a small hybrid kernel similar to the microkernel prototype described in the existing plans.
