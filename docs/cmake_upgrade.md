# CMake Build Workflow

The project now uses a modern CMake build system with **clang** and **bison**.  Earlier revisions documented migrating from the historical `bmake` setup; that transition is complete.

## 1. Prepare the environment

Install the toolchain as described in [setup_guide.md](setup_guide.md). CMake
will detect these tools automatically. Ensure `YACC="bison -y"` is exported in
your shell.

By default the top-level `CMakeLists.txt` enables a modest set of
SSE2-related optimizations when configuring on x86‑64.  These flags
(`-march=x86-64 -mmmx -msse -msse2`) provide a baseline that works on
all 64‑bit processors.  Pass `-DENABLE_NATIVE_OPT=OFF` if you need to
disable them or supply custom `CMAKE_C_FLAGS` values.

## 2. Create CMakeLists.txt next to each Makefile

Start by introducing small `CMakeLists.txt` files beside the existing makefiles.  Mirror the source lists and include paths from the makefiles.  Use `add_library()` or `add_executable()` targets with the same output names.

Example skeleton:

```cmake
cmake_minimum_required(VERSION 3.16)
project(example C)

add_library(example STATIC example.c)
```

Configure the project with CMake. Clang is the only supported compiler
and is selected automatically:

```sh
cmake -S . -B build -G Ninja
cmake --build build
```

## 3. Replace yacc rules with bison

For sources generated from `.y` files, use `BISON_TARGET()` from the CMake built-in Bison module.  Update the old `yacc` make rules to invoke the generated targets.

```cmake
find_package(BISON REQUIRED)
BISON_TARGET(parser parser.y ${CMAKE_CURRENT_BINARY_DIR}/parser.c)
add_library(parser STATIC ${BISON_parser_OUTPUTS})
```

## 4. Incrementally convert subdirectories

Convert each subdirectory in the tree and add it with `add_subdirectory()` from the top-level `CMakeLists.txt`.  Retain the existing makefiles until everything builds with CMake.

## 5. Clean up old Makefiles

Most makefiles have now been deleted. A few remain while their CMake
equivalents are validated. Future contributions should use CMake and
Ninja exclusively.

