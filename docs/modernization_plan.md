# Modernization Plan

This document outlines initial steps toward analyzing and updating the 4.4BSD-Lite2
codebase. It does not constitute a complete refactor, but provides guidance for
future work.

For a summary of directory mappings during the reorganization see
[fhs_migration.md](fhs_migration.md).

## Phase 1: Codebase Analysis
- Generate cross-reference databases using `cscope` and `ctags`.
- Use `python3 tools/analyze_codebase.py` to count source files by extension.
- Generate an include dependency graph with `python3 tools/generate_dependency_graph.py`.
  Use `--include-prefix` for additional header locations and
  `--ignore-unresolved-includes` to drop missing headers from the graph.
- Run `make -C tools dependency-graph` (via `tools/update_dependency_graph.sh`) to refresh `docs/dependency_graph.dot`.
- Document architectural assumptions found in headers and assembly files.

## Phase 2: Infrastructure Updates
- Configure modern compilers (e.g., GCC or Clang) with `-std=c2x`.
- Maintain compatibility with existing BSD makefiles while introducing
  modern build options.
- Prototype CMake build files using **CMake 3.16+** to evaluate a cross-platform build system.  See `cmake_upgrade.md` for a directory-by-directory migration plan.
- Integrate static analysis tools such as `clang-tidy`.
- Set up a `pre-commit` hook to run `clang-format` and `clang-tidy`.
- Generate a `compile_commands.json` database using `compiledb` for use with
  static analysis.

## Phase 3: Userland Modernization
- Update core libraries (`libc`, `libm`) to use ANSI C prototypes.
- Replace unsafe string functions with bounded equivalents.
- Introduce incremental tests for updated utilities.

## Phase 4: Kernel Abstraction
- Define a hardware abstraction layer to encapsulate architecture-specific
  operations.
- Begin refactoring scheduler and memory management code to use the HAL.

## Phase 5: Device Driver Migration
- Categorize drivers by interface type and update them to use the HAL.

## Phase 6: Integration and Validation
- Establish continuous integration builds for i686 and x86_64 targets.
  The GitHub workflow now compiles each architecture with GCC and Clang using
  `-m32` or `-m64` flags.

- Update library makefiles to honor `CFLAGS`/`LDFLAGS` so both architectures
  link properly.
- Track regression tests and performance benchmarks.


When the overall source lines of code (SLOC) exceed budget, modules can be pruned to keep the project manageable. Experimental drivers that are not required for the main target hardware and userland servers that have no active use should be removed first. A module qualifies for pruning when it lacks test coverage, has no known downstream consumers, or duplicates functionality already provided elsewhere in the tree. This trimming keeps the codebase under the SLOC limit while focusing modernization efforts on well-supported components.

### Tool failures
- pre-commit: command not found when running pre-commit hooks.

