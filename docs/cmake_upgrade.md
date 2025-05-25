# Transitioning from bmake to CMake

This guide outlines a gradual approach to replace the historical `bmake` build system with a modern CMake workflow that leverages **clang** and **bison**.  The steps can be applied directory by directory so that existing makefiles continue to work during the migration.

## 1. Prepare the environment

Run `setup.sh` to install clang, bison and the other toolchain components.  CMake will detect these automatically.  Ensure `YACC="bison -y"` is exported in your shell.

```sh
sudo ./setup.sh
```

## 2. Create CMakeLists.txt next to each Makefile

Start by introducing small `CMakeLists.txt` files beside the existing makefiles.  Mirror the source lists and include paths from the makefiles.  Use `add_library()` or `add_executable()` targets with the same output names.

Example skeleton:

```cmake
cmake_minimum_required(VERSION 3.16)
project(example C)

add_library(example STATIC example.c)
```

Invoke the compiler explicitly with clang when configuring:

```sh
CC=clang cmake -S . -B build -G Ninja
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

## 5. Remove bmake when no longer needed

Once every module builds via CMake, the legacy makefiles can be deleted and references to `bmake` in the documentation removed.  The build instructions in [building_kernel.md](building_kernel.md) already show how to invoke CMake.

