# Exokernel Subsystem Mapping

This reference records where each kernel component from the microkernel plan will live when building the exokernel variant.  The original 4.4BSD-Lite2 sources remain under `sys/` or `sys/dev/` for historical purposes.  New implementations are placed either in `src-kernel/` for code that stays in the kernel or in `src-uland/servers/` for user-space services.

| Subsystem | Original location | Target directory | Renaming notes |
|-----------|------------------|-----------------|----------------|
| Console driver | `sys/dev/cons*` | `src-uland/servers/` | no new name defined |
| File server | `sys/kern/vfs*` | `src-uland/servers/` | no new name defined |
| Process manager | `sys/kern/kern_proc.c` | `src-uland/servers/` | no new name defined |
| Scheduler | `sys/kern/kern_sched.c` | `src-uland/servers/` | no new name defined |
| Virtual memory manager | `sys/vm/` | `src-uland/servers/` | no new name defined |
| Device drivers | `sys/dev/*` | `src-uland/servers/` | drivers compiled as separate tasks |
