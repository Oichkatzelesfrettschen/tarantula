# Modernization Plan

This document outlines initial steps toward analyzing and updating the 4.4BSD-Lite2
codebase. It does not constitute a complete refactor, but provides guidance for
future work.

For a summary of directory mappings during the reorganization see
[fhs_migration.md](fhs_migration.md).

## Phase 1: Codebase Analysis
- Generate cross-reference databases using `cscope` and `ctags`.
- Use `python3 tools/analyze_codebase.py` to count source files by extension.
- Document architectural assumptions found in headers and assembly files.

## Phase 2: Infrastructure Updates
- Configure modern compilers (e.g., GCC or Clang) with `-std=c2x`.
- Maintain compatibility with existing BSD makefiles while introducing
  modern build options.
- Prototype CMake build files using **CMake 3.16+** to evaluate a cross-platform build system.
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

