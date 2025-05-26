# C23 and Modern Assembly Refactor Scoping

This document captures initial observations of the repository layout, environment details, and a high level plan for refactoring the 4.4BSD-Lite2 sources to conform to the C23 standard and employ modern assembly practices where applicable.

## Environment

- Kernel: `Linux 6.12.13 x86_64`
- GCC version: `gcc (Ubuntu 13.3.0-6ubuntu2~24.04) 13.3.0`
- Clang version: `clang version 17.0.0 (https://github.com/swiftlang/llvm-project.git 901f89886dcd5d1eaf07c8504d58c90f37b0cfdf)`

These compilers support the upcoming C23 (C2x) standard and provide modern toolchains for assembly generation.

## Repository Overview

A summary of the top level directories is provided by `docs/file_tree.txt`.

```
.
.git
  branches
  hooks
  info
  logs
  objects
  refs
Domestic
  src
Foreign
  src
dev
docs
etc
  kerberosIV
  mtree
  namedb
root
tools
usr
  bin
  lib
  share
  src
  ucb
var
  log
  run
```

## Proposed Agent Tasks

1. **Codebase Enumeration**
   - Run `python3 tools/analyze_codebase.py` to obtain counts of source files by extension.
   - Generate cross references using `tools/generate_cscope.sh` and `tools/generate_ctags.sh`.
   - Document any existing assembly files (`.s`) and identify their architecture dependencies.

2. **Build System Modernization**
   - Update makefiles to accept `CC=c23` style flags while preserving historical builds.
   - Introduce CI scripts targeting GCC and Clang with `-std=c2x`.
   - Record build warnings for later remediation.

3. **API Updates**
   - Gradually adopt C23 features (e.g., standard attributes, `_Static_assert` usage) in the libc and kernel headers.
   - Replace legacy types and macros with modern equivalents.

4. **Assembly Review**
   - For each architecture directory under `sys/` and `usr/src`, note any inline or external assembly.
   - Evaluate portability of the code and consider rewriting small routines in intrinsics or modern assembly syntax (e.g., GNU `asm`).

5. **File-by-File Refactor**
   - Prioritize userland utilities in `usr/` for initial conversion.
   - Develop automated scripts to apply consistent formatting and header updates.
   - Introduce small unit tests wherever feasible.

6. **Documentation**
   - Keep this document updated with progress notes and decisions.
   - Reference coding standards and style guidelines as the project evolves.

This roadmap is intentionally high level. Full conversion of the 4.4BSD-Lite2 tree to C23 will require significant long-term effort and careful testing. The above tasks serve as an initial direction for agents working on the modernization.

## Recent Progress

- Added a `CSTD` variable to `share/mk/sys.mk` so builds can pass `CSTD=-std=c2x`.
- Introduced a fallback definition of `_Static_assert` in `sys/sys/cdefs.h` to
  allow compile-time checks on pre-C11 compilers.
- Created a workflow in `.github/workflows/build.yml` to build the tree with
  both GCC and Clang using the C23 standard flag.
- New script `tools/build_collect_warnings.sh` builds the tree and captures
  compiler warnings for later cleanup.
- CI now builds for both `x86_64` and `i686` using `-m64` and `-m32` flags.
- `tools/build_collect_warnings.sh` accepts an `ARCH` variable to set these
  flags when collecting warnings.
- `usr/src/libpathtrans` now respects `CFLAGS` and `LDFLAGS` so cross-
  architecture builds link correctly.
- Added a `CSTD` variable to all makefiles under `engine/src-uland/` and
  appended it to `CFLAGS` so these components build with C23 by default.

## Lazy Generation-based Revocation

Earlier drafts suggested invoking a `zero_entire_pml` routine whenever a
process had its address space revoked.  That approach eagerly cleared
all mappings and forced every CPU to flush its view of the page tables.

Instead, store a small **epoch** counter in each PTE.  Each CPU maintains
its own epoch value.  When global revocation is required, the system
simply increments the current epoch without touching individual PTEs.

If a CPU accesses a PTE whose epoch differs from its local epoch, a page
fault occurs.  The fault handler checks the epoch, updates the entry to
match the CPU's epoch, and re-establishes or discards the mapping as
appropriate.  This lazy check avoids unnecessary TLB shootdowns while
ensuring revoked mappings cannot be used.

Periodic reconciliation walks the CPUs and advances any stale epoch
counters.  This keeps the per-CPU epochs bounded so old generations do
not linger indefinitely.

- Created `engine/src-headers/arch.h` with C23 macros to detect 16-, 32- and 64-bit
  architectures.
- Added a new `ports/` tree containing initial Chicken Scheme and Go stubs.
- Modernized `engine/src-headers/compat/svr4/svr4_machdep.h` with fixed-width types and
  a `_Static_assert` to verify register counts.
