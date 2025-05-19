# Microkernel Extraction Plan

This document sketches out an incremental approach for isolating select subsystems from the monolithic 4.4BSD-Lite2 kernel.  The goal is to experiment with a microkernel design while preserving the historical sources.

## Candidate subsystems

The following components under `sys/kern` and `sys/dev` are early candidates for separation:

- **Console driver** – move basic console I/O (`sys/dev/cons*`) into a user-space service.
- **File server** – extract VFS logic from `sys/kern/vfs*` and expose it as a standalone file server.
- **Process manager** – run `sys/kern/kern_proc.c` functionality in a dedicated manager handling fork/exec.
- **Scheduler** – refactor `sys/kern/kern_sched.c` to operate as a pluggable scheduling module.
- **Virtual memory manager** – split the VM subsystem (currently under `sys/vm`) for use as a memory service.
- **Device drivers** – SCSI and network adapters from `sys/dev` compiled as independent driver tasks.

These subsystems will initially build as normal kernel objects.  As the microkernel takes shape they can be compiled into user-space servers or loadable modules.

## Maintaining historical files

To keep provenance, the original sources remain under `sys/kern` and `sys/dev`.  New implementations should live in separate directories (for example `servers/` or `modules/`) with comments referencing the original file paths.  This allows archival copies to stay untouched while new code evolves.

