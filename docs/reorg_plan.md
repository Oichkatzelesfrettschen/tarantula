# Reorganization Plan

This document outlines tasks for flattening the 4.4BSD-Lite2 source tree and modernizing the build system. The goal is to restructure the project into a POSIX-compliant layout while preserving historical sources.

## Task Breakdown

1. **Code Auditor** – Catalog all source files and note deviations from POSIX/ISO standards.
2. **Build System Engineer** – Convert makefiles and scripts for portable builds.
3. **Source Librarian** – Restructure directories, maintain symlinks, and update documentation.
4. **Compiler/Toolchain Expert** – Modernize code, remove non-standard constructs, and ensure it compiles under a contemporary POSIX environment.
5. **Testing Lead** – Set up automated builds and regression tests.

## Implementation Steps

1. Generate an inventory of files using `tools/create_inventory.py`.
2. Draft new makefiles under `src/`, `include/`, `lib/`, and `tests/`.
3. Incrementally refactor C sources to ANSI prototypes and replace legacy headers.
4. Compile each subsystem with modern compilers and run tests.
5. Document all changes and keep references to original paths for traceability.
6. Convert the historic directory layout using `tools/migrate_to_fhs.sh` and
   maintain compatibility symlinks during the transition.
7. Reorganize kernel and userland sources with
   `tools/migrate_to_src_layout.sh` (or the older `tools/organize_sources.sh`)
   to move them into `src-kernel`, `src-uland`, `src-headers` and `src-lib`.

