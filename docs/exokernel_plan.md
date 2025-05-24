# Exokernel Migration Plan

This document outlines how to evolve the 4.4BSD-Lite2 sources toward an exokernel architecture. It complements the microkernel tasks by focusing on exposing hardware resources directly to user programs while the kernel acts only as a secure multiplexer. See [microkernel_plan.md](microkernel_plan.md) for the related microkernel roadmap.

## Microkernel vs. Exokernel

* **Microkernel** designs still implement core services such as scheduling, memory management and interprocess communication inside the kernel. Other components run as user-space servers.
* **Exokernel** kernels reduce their role even further. They provide low-level protection and resource allocation primitives without imposing high-level abstractions. User libraries and servers implement process management, virtual memory policies and filesystems.

## Goals

1. Minimize in-kernel services to just safe multiplexing of CPU, memory and devices.
2. Move policy decisions (scheduling, paging, file layout) to user-level managers.
3. Retain historical sources under `sys/` while experimenting with exokernel replacements in new directories.

## Directory Layout

The layout introduced in the microkernel plan remains with slight changes:

- `src-kernel/` – exokernel core providing only protection and low-level resource handling.
- `src-uland/` – user-level libraries and servers that implement traditional OS functionality.
- `include/` – headers shared between the exokernel and user components. The
  `exokernel.h` header declares stub entry points `kern_sched_init`,
  `kern_open` and `kern_vm_fault`.
- The specific subsystems being moved are listed in
[exokernel_subsystems.md](exokernel_subsystems.md).

Steps from `tools/migrate_to_fhs.sh` still place these directories under `/usr` during migration. See [fhs_migration.md](fhs_migration.md) for details.

## Refactor Steps

1. **Inventory**
   - Use `python3 tools/create_inventory.py` as described in [building_kernel.md](building_kernel.md) to capture the current tree.
2. **Kernel Minimization**
   - Strip existing kernel files to a bare allocator, context switch code and interrupt handlers.
   - Provide system calls for safe access to hardware resources (CPU time slices, memory pages, I/O ports).
3. **User-Level Resource Managers**
   - Port the scheduler, virtual memory manager and filesystem logic from `sys/` into libraries under `src-uland/`.
   - Each manager communicates with the exokernel through the new low-level API.

### tlb_sync() and Platform-Specific Queues

The planned IOMMU domain object (`src-kernel/iommu/domain.c`,
`include/iommu/domain.h`) implements `tlb_sync()` as a wrapper that
expands into architecture specific queue commands:

* **Intel VT-d** &ndash; `tlb_sync()` inserts a queue invalidation descriptor
  and waits for the associated completion status before returning.
* **AMD-Vi** &ndash; the call formats a command entry in the device queue,
  polling the completion field referenced by the queued event ID.
* **ARM SMMU** &ndash; `tlb_sync()` issues a `TLBI` command followed by a
  `SYNC` entry to ensure the command queue has drained.

This routine guarantees that DMA mappings are visible to hardware before
control is returned to user code.
4. **Build System Updates**
   - Update makefiles so the exokernel and user managers build separately but link during installation.
   - Continue following the FHS migration guide to ensure files end up under `/usr/src-kernel` and `/usr/src-uland`.
5. **Testing**
   - Compile the exokernel following the steps in [building_kernel.md](building_kernel.md).
   - Boot with minimal services to validate that user-level managers can start and allocate resources correctly. See [exokernel_testing.md](exokernel_testing.md) for a detailed walkthrough.

## Mapping FHS Tasks

The migration steps in [fhs_migration.md](fhs_migration.md) apply unchanged. `python3 tools/create_inventory.py` records new directories, and `tools/migrate_to_fhs.sh` copies them under `/usr`. Build scripts should reference the `/usr` paths once the migration is complete.

