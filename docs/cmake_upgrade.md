# Transitioning from bmake to CMake

This guide originally described a gradual approach to replace the historical `bmake` build system with a modern CMake workflow that leverages **clang** and **bison**.  The repository has now completed this transition and all remaining Makefiles have been removed.

## 1. Prepare the environment

Run `setup.sh` to install clang, bison and the other toolchain components.  Codex environments may call `.codex/setup.sh`, which wraps this script and installs extra verification tools.  CMake will detect these automatically.  Ensure `YACC="bison -y"` is exported in your shell.

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

Originally each subdirectory was ported one at a time using
`add_subdirectory()` while the old makefiles remained.  The conversion is
now complete and every target builds with CMake.  Future contributions
should rely solely on CMake and Ninja.

