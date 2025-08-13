# Modern Architecture, Design and Implementation Guide

This reference gathers the scattered notes within the repository into a single
design document. It records progress so far and explains how the project moves
toward a C23-based microkernel and eventual exokernel.

## 1. Repository Analysis

The helper script `tools/analyze_codebase.py` counts the active sources:

```
.c: 6023
.f: 2
.h: 3293
.l: 29
.s: 395
.sh: 167
.y: 39
```

Attempts to run **cloc**, **lizard** and **cscope** failed because these tools
are not available in the current environment, so only the built-in inventory is
listed.

## 2. Source Tree Overview

The tree mirrors the historic 4.4BSD-Lite2 layout while adding modern
directories described in [SOURCE_TREE_OVERVIEW.md](../SOURCE_TREE_OVERVIEW.md):

- `src-kernel/` – C23-compliant stubs that forward calls to the legacy
  `sys/` kernel using the mailbox API detailed in [IPC.md](IPC.md).
- `src-uland/` – user-space servers and libraries replacing monolithic
  kernel subsystems.
- `src-lib/` – archive libraries separated from the historical tree.
- `src-headers/` – exported headers for user-space managers.

Scripts under `tools/` generate inventories and dependency graphs while the
`docs/` folder tracks migration tasks in depth.

## 3. Design Vision

### 3.1 Microkernel Foundations

Only minimal functionality remains in kernel space:

1. **Thread Scheduling Hooks** – policy handled by a user-space scheduler.
2. **Virtual Memory Hooks** – faults forwarded to a memory manager
   library with emergency reserves.
3. **Kernel Allocator** – slab allocator with per-CPU caches as outlined in
   [memory_allocator.md](memory_allocator.md).
4. **IPC Mechanism** – ring-buffer mailboxes passing `struct ipc_message`
   instances.

Device drivers, file systems and process managers become user-space services
communicating through these hooks.

### 3.2 Exokernel Path

The exokernel variant further reduces kernel duties to protection and resource
allocation. Key steps from [exokernel_plan.md](exokernel_plan.md) and
[exokernel_subsystems.md](exokernel_subsystems.md) include:

1. Moving the scheduler, VM policy and file server into
   `src-uland/servers/`.
2. Compiling device drivers as independent tasks with capability handles.
3. Providing a small runtime library so applications construct higher-level
   abstractions.
4. Using formal models under `docs/formal/` to verify capability revocation and
   memory safety.

## 4. Implementation Roadmap

The modernization phases combine notes from
[modernization_plan.md](modernization_plan.md),
[microkernel_plan.md](microkernel_plan.md) and
[reorg_plan.md](reorg_plan.md):

1. **Inventory and Build Updates** – generate the file inventory and introduce
   CMake alongside historical makefiles.
2. **Directory Reorganization** – migrate sources using `migrate_to_fhs.sh` and
   `migrate_to_src_layout.sh` so active development occurs under `src-*` paths.
3. **Subsystem Extraction** – move scheduling, VM and driver code to user space
   while keeping compatibility symlinks.
4. **Testing and Validation** – expand the test suite and build for multiple
   architectures using the instructions in [building_kernel.md](building_kernel.md).

## 5. Modern C23 Guidelines

New code follows upcoming C23 conventions:

- Use explicit `bool` and `size_t` types instead of legacy flags.
- Annotate seldom-used parameters with `[[maybe_unused]]`.
- Declare module-local functions `static` and `inline` where useful.
- Prefer designated initializers for clarity.
- Apply `static_assert` to enforce invariants.
- Limit assembly to small, well-documented snippets via intrinsics.

## 6. Toolchain Strategy

The environment provisioning step installs utilities that aid analysis and documentation:

- **cloc** for language statistics.
- **lizard** for cyclomatic complexity.
- **cscope** for cross-references.
- **cflow** for call graphs.
- **plantuml** for sequence and component diagrams.
- **gprof2dot** for visualizing profiler output.

These tools may need network access or pre-downloaded packages to install.

## 7. Conclusion

The refactor aims to evolve the historical tree into a modern C23 system with a
microkernel core and optional exokernel variant. The roadmap outlined above
captures the remaining tasks and references supporting documents so future
contributors can follow a consistent strategy.
