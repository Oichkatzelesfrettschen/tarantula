cmake_minimum_required(VERSION 3.16)

#Default to clang if no compiler was specified at configure time so callers
#can override these via - DCMAKE_C_COMPILER and -DCMAKE_CXX_COMPILER.
if(NOT DEFINED CMAKE_C_COMPILER)
  set(CMAKE_C_COMPILER clang)
endif()
if(NOT DEFINED CMAKE_CXX_COMPILER)
  set(CMAKE_CXX_COMPILER clang++)
endif()

project(tarantula C)
set(CMAKE_C_STANDARD 23)

# Optionally enable x86-64 specific optimizations. These flags target
# baseline 64-bit CPUs with SSE2 and MMX support. The option defaults to
# ON so users get reasonable performance out of the box, but it can be
# disabled or overridden by specifying custom CMAKE_C_FLAGS/CMAKE_CXX_FLAGS.
option(ENABLE_NATIVE_OPT "Use x86-64 SSE2 optimizations" ON)

if(ENABLE_NATIVE_OPT AND CMAKE_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64|AMD64)$")
  set(_NATIVE_FLAGS "-march=x86-64 -mmmx -msse -msse2")
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${_NATIVE_FLAGS}")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${_NATIVE_FLAGS}")
endif()
find_package(BISON)
if(BISON_FOUND)
  message(STATUS "Bison found: ${BISON_EXECUTABLE}")
else()
  message(WARNING "bison not found - some tools may not build")
endif()

add_library(ipc STATIC src-lib/libipc/ipc.c)
target_include_directories(ipc PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/include)

add_library(posix STATIC src-lib/libposix/posix.c)
target_include_directories(posix PUBLIC ${CMAKE_SOURCE_DIR}/src-headers)

add_library(kern_stubs STATIC
  src-kernel/proc_hooks.c
  src-kernel/sched_hooks.c
  src-kernel/vm_hooks.c
  src-kernel/vfs_hooks.c
)
target_include_directories(kern_stubs PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/include)
target_link_libraries(kern_stubs PUBLIC ipc)

file(GLOB FS_SERVER_SRC src-uland/fs-server/*.c)
add_executable(fs_server ${FS_SERVER_SRC})
target_include_directories(fs_server PRIVATE
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/src-headers/machine
  ${CMAKE_SOURCE_DIR}/sys
  ${CMAKE_SOURCE_DIR}/sys/sys
  ${CMAKE_SOURCE_DIR}/sys/i386/include)
target_compile_definitions(fs_server PRIVATE KERNEL)
target_link_libraries(fs_server PRIVATE ipc)

install(FILES src-headers/arch.h DESTINATION include)


