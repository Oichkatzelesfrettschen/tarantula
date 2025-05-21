# Microkernel Extraction Plan

This document sketches out an incremental approach for isolating select subsystems from the monolithic 4.4BSD-Lite2 kernel.  The goal is to experiment with a microkernel design while preserving the historical sources.

## Overview
This plan transitions the monolithic BSD kernel into a minimal microkernel and moves device drivers and system servers into user space. Steps reference the FHS migration guide and the roles listed in reorg_plan.md.

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


# Microkernel Refactor Plan

This document proposes a high level roadmap for converting the current 4.4BSD-Lite2 kernel into a microkernel. It builds on the tasks described in [fhs_migration.md](fhs_migration.md) and references the roles defined in [reorg_plan.md](reorg_plan.md) so agents know how responsibilities shift.

## Goals
- Isolate core kernel functionality (scheduling, memory management and interprocess communication) into a minimal microkernel.
- Move file systems, networking stacks and device drivers to user space servers.
- Maintain compatibility with existing userland utilities during the transition.

## Directory Layout
To keep the historic sources intact while adopting a microkernel approach, new directories are introduced alongside the FHS migration:

- `src-kernel/` – microkernel sources replacing the traditional `sys/` tree.
- `src-uland/` – user space servers and drivers derived from `usr/src` and `libexec`.
- `src-tools/` – build utilities currently found in `tools/`.
- `include/` – headers shared between the microkernel and user space components.

The steps in `tools/migrate_to_fhs.sh` will be updated so these directories map under `/usr` inside a chroot, e.g. `/usr/src-kernel` and `/usr/src-uland`. Compatibility symlinks from `sys/` and `usr/src/` are kept until the new layout is stable.

## Refactor Steps and Role Assignments
1. **Inventory and Preparation**
   - The **Code Auditor** catalogs kernel components and notes dependencies between drivers and core subsystems.
   - The **Source Librarian** creates the `src-kernel` and `src-uland` directories, copying files from `sys/` and `usr/src/` while generating symlinks for backward compatibility.
   - A run of `tools/create_inventory.py` records the baseline tree in `docs/file_inventory.txt`.

2. **Build System Updates**
   - The **Build System Engineer** drafts makefiles for `src-kernel` and `src-uland` so they build independently.
   - Update `tools/migrate_to_fhs.sh` to place these directories under `/usr` during migration.
   - Existing FHS tasks such as verifying symlinks and updating scripts continue to apply, but now reference the new directories.

3. **Microkernel Extraction**
   - The **Compiler/Toolchain Expert** moves scheduler, VM and IPC code into `src-kernel`.
   - Device drivers and BSD daemons become user space services under `src-uland/servers` and `src-uland/drivers`.

4. **User Space Isolation**
   - Servers communicate with the microkernel via message passing or shared memory APIs.
   - Build scripts ensure these servers run with minimal privileges, mirroring modern microkernel designs.

5. **Testing and Validation**
   - The **Testing Lead** sets up parallel builds for the monolithic kernel and the evolving microkernel layout.
   - Regression tests ensure that userland tools still operate correctly when services move out of kernel space.

6. **Iterative Migration**
   - After each milestone, rerun `tools/create_inventory.py` and update `docs/file_inventory.txt`.
   - Document new paths and symlinks so historical references remain clear.
   - Continue following the FHS migration guide for any remaining directories.

## Mapping FHS Tasks to the New Layout
The migration steps listed in [fhs_migration.md](fhs_migration.md) apply to the new directories as follows:

1. `tools/create_inventory.py` records both `src-kernel` and `src-uland` alongside existing paths.
2. `tools/migrate_to_fhs.sh --dry-run` previews copying these directories under `/usr` (`/usr/src-kernel`, `/usr/src-uland`).
3. Running the script without `--dry-run` performs the copy and replaces the old locations with symlinks.
4. Makefiles and scripts are updated to reference the `/usr` paths, ensuring builds occur in the new structure.
5. Compatibility links are gradually removed once everything builds cleanly.

Following this plan will separate kernel responsibilities into a microkernel while reusing the FHS migration workflow and the role-based tasks from `reorg_plan.md`.

## Organizing Sources Under `src-*`

After completing the FHS migration steps (running `migrate_to_fhs.sh` and
`post_fhs_cleanup.sh` as described in [fhs_migration.md](fhs_migration.md)), the
repository can be reorganized so that code lives under the `src-*` directories.
Use `tools/organize_sources.sh` to perform this move. Preview the changes with:

```sh
tools/organize_sources.sh --dry-run
```

When executed without `--dry-run`, the script relocates `sys/` into
`src-kernel/` and `usr/src/` into `src-uland/`, leaving symlinks at the original
paths. Running it after the migration scripts ensures the microkernel build
operates on the consolidated layout referenced throughout this plan.

