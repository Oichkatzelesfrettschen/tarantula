cmake_minimum_required(VERSION 3.16)

add_executable(reincarnation
    reincarnation.c
)

target_include_directories(reincarnation PRIVATE
    ${CMAKE_SOURCE_DIR}/src-headers
    ${CMAKE_SOURCE_DIR}/src-uland/libipc
    ${CMAKE_SOURCE_DIR}/include
)

target_link_libraries(reincarnation PRIVATE ipc)

target_compile_options(reincarnation PRIVATE -Wall -Werror -O2)

