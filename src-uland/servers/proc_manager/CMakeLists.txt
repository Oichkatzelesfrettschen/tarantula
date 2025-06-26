cmake_minimum_required(VERSION 3.16)

add_executable(proc_manager
    kern_proc.c
    pm_entry.c
)

target_include_directories(proc_manager PRIVATE
    ${CMAKE_SOURCE_DIR}/src-headers
    ${CMAKE_SOURCE_DIR}/src-headers/machine
    ${CMAKE_SOURCE_DIR}/sys
    ${CMAKE_SOURCE_DIR}/sys/sys
    ${CMAKE_SOURCE_DIR}/sys/i386/include
    ${CMAKE_SOURCE_DIR}/include
)

target_compile_definitions(proc_manager PRIVATE KERNEL)

target_compile_options(proc_manager PRIVATE -Wall -Werror -O2)

