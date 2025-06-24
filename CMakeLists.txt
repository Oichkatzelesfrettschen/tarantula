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

# When using Clang, compile for a baseline x86 CPU and enable
# SSE2/MMX support.  The baseline can be overridden with
# -DBASELINE_CPU=<arch> at configure time.
if(CMAKE_C_COMPILER_ID STREQUAL "Clang")
  set(BASELINE_CPU "x86-64-v1" CACHE STRING "Architecture passed to -march")
  set(BASE_CFLAGS -march=${BASELINE_CPU} -msse2 -mmmx -mfpmath=sse -O3)
  set(BASE_LDFLAGS -fuse-ld=lld)
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

# Apply baseline compile and link options to all targets when using Clang.
if(CMAKE_C_COMPILER_ID STREQUAL "Clang")
  set(ALL_TARANTULA_TARGETS ipc posix kern_stubs fs_server)
  foreach(t ${ALL_TARANTULA_TARGETS})
    target_compile_options(${t} PRIVATE ${BASE_CFLAGS})
    target_link_options(${t} PRIVATE ${BASE_LDFLAGS})
  endforeach()
endif()


