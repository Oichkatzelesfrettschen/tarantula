cmake_minimum_required(VERSION 3.16)

# ---------------------------------------------------------------------------
# Project definition and language
# ---------------------------------------------------------------------------
project(tarantula LANGUAGES C)
set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# ---------------------------------------------------------------------------
# Default compiler selection (overrideable via -DCMAKE_C_COMPILER)
# ---------------------------------------------------------------------------
if(NOT DEFINED CMAKE_C_COMPILER)
  set(CMAKE_C_COMPILER clang)
endif()
if(NOT DEFINED CMAKE_CXX_COMPILER)
  set(CMAKE_CXX_COMPILER clang++)
endif()

# ---------------------------------------------------------------------------
# Native optimization flags
# ---------------------------------------------------------------------------
option(ENABLE_NATIVE_OPT "Enable baseline x86-64-v1 + SSE2 + MMX optimizations" ON)

if(ENABLE_NATIVE_OPT AND CMAKE_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64|AMD64)$")
  message(STATUS "Enabling x86-64-v1 + SSE2 + MMX optimizations")
  add_compile_options(
    -march=x86-64-v1
    -msse2
    -mmmx
    -mfpmath=sse
  )
endif()

# ---------------------------------------------------------------------------
# Default C flags (optimization + linker)
# ---------------------------------------------------------------------------
set(CMAKE_C_FLAGS
    "${CMAKE_C_FLAGS} -O3 -fuse-ld=lld"
)
set(CMAKE_CXX_FLAGS
    "${CMAKE_CXX_FLAGS} -O3 -fuse-ld=lld"
)

# ---------------------------------------------------------------------------
# Bison detection
# ---------------------------------------------------------------------------
find_package(BISON)
if(BISON_FOUND)
  message(STATUS "Bison found: ${BISON_EXECUTABLE}")
else()
  message(WARNING "Bison not found; some tools may not build")
endif()

# ---------------------------------------------------------------------------
# IPC library
# ---------------------------------------------------------------------------
add_library(ipc STATIC
  src-lib/libipc/ipc.c
)
target_include_directories(ipc PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/include
)

# ---------------------------------------------------------------------------
# POSIX compatibility library
# ---------------------------------------------------------------------------
add_library(posix STATIC
  src-lib/libposix/posix.c
)
target_include_directories(posix PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
)

# ---------------------------------------------------------------------------
# Kernel stubs
# ---------------------------------------------------------------------------
add_library(kern_stubs STATIC
  src-kernel/proc_hooks.c
  src-kernel/sched_hooks.c
  src-kernel/vm_hooks.c
  src-kernel/vfs_hooks.c
)
target_include_directories(kern_stubs PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/include
)
target_link_libraries(kern_stubs PUBLIC ipc)

# ---------------------------------------------------------------------------
# Filesystem server
# ---------------------------------------------------------------------------
file(GLOB FS_SERVER_SRC
  src-uland/fs-server/*.c
)
add_executable(fs_server ${FS_SERVER_SRC})
target_include_directories(fs_server PRIVATE
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/src-headers/machine
  ${CMAKE_SOURCE_DIR}/sys
  ${CMAKE_SOURCE_DIR}/sys/sys
  ${CMAKE_SOURCE_DIR}/sys/i386/include
)
target_compile_definitions(fs_server PRIVATE KERNEL)
target_link_libraries(fs_server PRIVATE ipc)

# ---------------------------------------------------------------------------
# Installation
# ---------------------------------------------------------------------------
install(FILES
  src-headers/arch.h
  DESTINATION include
)
