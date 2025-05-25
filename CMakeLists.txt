cmake_minimum_required(VERSION 3.16)
project(tarantula C)

find_package(BISON)
if(BISON_FOUND)
  message(STATUS "Bison found: ${BISON_EXECUTABLE}")
else()
  message(WARNING "bison not found - some tools may not build")
endif()

add_library(ipc STATIC src-lib/libipc/ipc.c)
target_include_directories(ipc PUBLIC ${CMAKE_SOURCE_DIR}/src-headers)

add_library(pthread_compat STATIC src-lib/pthread/pthread.c)
target_include_directories(pthread_compat PUBLIC ${CMAKE_SOURCE_DIR}/src-headers)

add_library(kern_stubs STATIC
  src-kernel/proc_hooks.c
  src-kernel/sched_hooks.c
  src-kernel/vm_hooks.c
  src-kernel/vfs_hooks.c
)
target_include_directories(kern_stubs PUBLIC ${CMAKE_SOURCE_DIR}/src-headers)
target_link_libraries(kern_stubs PUBLIC ipc)

file(GLOB FS_SERVER_SRC src-uland/fs-server/*.c)
add_executable(fs_server ${FS_SERVER_SRC})
target_include_directories(fs_server PRIVATE
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/src-headers/machine
  ${CMAKE_SOURCE_DIR}/sys
  ${CMAKE_SOURCE_DIR}/sys/sys
  ${CMAKE_SOURCE_DIR}/sys/i386/include)
target_compile_definitions(fs_server PRIVATE KERNEL)
target_link_libraries(fs_server PRIVATE ipc)


