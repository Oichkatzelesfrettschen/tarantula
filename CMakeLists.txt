cmake_minimum_required(VERSION 3.16)

# ────────────────────────────────────────────────────────────────────────────
# Project definition and language
# ────────────────────────────────────────────────────────────────────────────
project(tarantula LANGUAGES C)

# Require C23, no compiler‐specific extensions
set(CMAKE_C_STANDARD        23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS      OFF)

# ────────────────────────────────────────────────────────────────────────────
# Default compiler selection (overrideable via -DCMAKE_C_COMPILER)
# ────────────────────────────────────────────────────────────────────────────
if(NOT DEFINED CMAKE_C_COMPILER)
  set(CMAKE_C_COMPILER clang)
endif()

# ────────────────────────────────────────────────────────────────────────────
# Analysis and Testing Options
# ────────────────────────────────────────────────────────────────────────────
option(ENABLE_COVERAGE "Enable code coverage instrumentation (gcov/lcov)" OFF)
option(ENABLE_ASAN "Enable AddressSanitizer" OFF)
option(ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer" OFF)
option(ENABLE_TSAN "Enable ThreadSanitizer" OFF)
option(ENABLE_MSAN "Enable MemorySanitizer" OFF)
option(ENABLE_CLANG_TIDY "Run clang-tidy static analysis" ON)
option(ENABLE_CPPCHECK "Run cppcheck static analysis" OFF)
option(ENABLE_LTO "Enable link-time optimization" OFF)
option(ENABLE_PGO_GEN "Enable profile-guided optimization (generation phase)" OFF)
option(ENABLE_PGO_USE "Enable profile-guided optimization (use phase)" OFF)

# ────────────────────────────────────────────────────────────────────────────
# Native optimization flags
# ────────────────────────────────────────────────────────────────────────────
option(ENABLE_NATIVE_OPT "Enable baseline x86-64 + SSE2 + MMX optimizations" ON)
set(BASELINE_CPU "x86-64" CACHE STRING "Architecture passed to -march")

# Initialize flag lists
set(BASE_CFLAGS)
set(BASE_LDFLAGS)

# Base optimization flags
if(ENABLE_NATIVE_OPT AND CMAKE_C_COMPILER_ID STREQUAL "Clang")
  message(STATUS "Enabling native optimizations: -march=${BASELINE_CPU} -msse2 -mmmx -mfpmath=sse -O3")
  list(APPEND BASE_CFLAGS
      -march=${BASELINE_CPU}
      -msse2
      -mmmx
      -mfpmath=sse
      -O3
  )
  list(APPEND BASE_LDFLAGS -fuse-ld=lld)
else()
  message(STATUS "Native optimizations disabled or non–Clang compiler detected; using -O3 only")
  list(APPEND BASE_CFLAGS -O3)
  list(APPEND BASE_LDFLAGS -fuse-ld=lld)
endif()

# Coverage instrumentation
if(ENABLE_COVERAGE)
  message(STATUS "Enabling code coverage instrumentation")
  list(APPEND BASE_CFLAGS --coverage -fprofile-arcs -ftest-coverage)
  list(APPEND BASE_LDFLAGS --coverage)
  # Create coverage targets
  add_custom_target(coverage
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/coverage
    COMMAND lcov --capture --directory ${CMAKE_BINARY_DIR} --output-file ${CMAKE_BINARY_DIR}/coverage/coverage.info
    COMMAND lcov --remove ${CMAKE_BINARY_DIR}/coverage/coverage.info '/usr/*' --output-file ${CMAKE_BINARY_DIR}/coverage/coverage.info
    COMMAND genhtml ${CMAKE_BINARY_DIR}/coverage/coverage.info --output-directory ${CMAKE_BINARY_DIR}/coverage
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Generating code coverage report"
  )
endif()

# AddressSanitizer
if(ENABLE_ASAN)
  message(STATUS "Enabling AddressSanitizer")
  list(APPEND BASE_CFLAGS -fsanitize=address -fno-omit-frame-pointer)
  list(APPEND BASE_LDFLAGS -fsanitize=address)
endif()

# UndefinedBehaviorSanitizer
if(ENABLE_UBSAN)
  message(STATUS "Enabling UndefinedBehaviorSanitizer")
  list(APPEND BASE_CFLAGS -fsanitize=undefined -fno-omit-frame-pointer)
  list(APPEND BASE_LDFLAGS -fsanitize=undefined)
endif()

# ThreadSanitizer
if(ENABLE_TSAN)
  message(STATUS "Enabling ThreadSanitizer")
  list(APPEND BASE_CFLAGS -fsanitize=thread)
  list(APPEND BASE_LDFLAGS -fsanitize=thread)
endif()

# MemorySanitizer
if(ENABLE_MSAN)
  message(STATUS "Enabling MemorySanitizer")
  list(APPEND BASE_CFLAGS -fsanitize=memory -fno-omit-frame-pointer)
  list(APPEND BASE_LDFLAGS -fsanitize=memory)
endif()

# Link-time optimization
if(ENABLE_LTO)
  message(STATUS "Enabling link-time optimization")
  list(APPEND BASE_CFLAGS -flto)
  list(APPEND BASE_LDFLAGS -flto)
endif()

# Profile-guided optimization
if(ENABLE_PGO_GEN)
  message(STATUS "Enabling PGO generation phase")
  list(APPEND BASE_CFLAGS -fprofile-generate)
  list(APPEND BASE_LDFLAGS -fprofile-generate)
elseif(ENABLE_PGO_USE)
  message(STATUS "Enabling PGO use phase")
  if(EXISTS "${CMAKE_SOURCE_DIR}/default.profdata")
    list(APPEND BASE_CFLAGS -fprofile-use=${CMAKE_SOURCE_DIR}/default.profdata)
  else()
    message(WARNING "PGO profile data not found at ${CMAKE_SOURCE_DIR}/default.profdata")
  endif()
endif()

# Apply flags globally to all C targets
add_compile_options(${BASE_CFLAGS})
add_link_options(${BASE_LDFLAGS})

# Static analysis integration
if(ENABLE_CLANG_TIDY)
  find_program(CLANG_TIDY_EXE NAMES clang-tidy)
  if(CLANG_TIDY_EXE)
    message(STATUS "Found clang-tidy: ${CLANG_TIDY_EXE}")
    set(CMAKE_C_CLANG_TIDY ${CLANG_TIDY_EXE} -checks=-*,clang-analyzer-*,modernize-*)
  else()
    message(WARNING "clang-tidy not found")
  endif()
endif()

if(ENABLE_CPPCHECK)
  find_program(CPPCHECK_EXE NAMES cppcheck)
  if(CPPCHECK_EXE)
    message(STATUS "Found cppcheck: ${CPPCHECK_EXE}")
    add_custom_target(cppcheck
      COMMAND ${CPPCHECK_EXE}
        --enable=all
        --inconclusive
        --xml
        --output-file=${CMAKE_BINARY_DIR}/cppcheck.xml
        ${CMAKE_SOURCE_DIR}/src-kernel
        ${CMAKE_SOURCE_DIR}/src-lib
        ${CMAKE_SOURCE_DIR}/src-uland
      COMMENT "Running cppcheck static analysis"
    )
  else()
    message(WARNING "cppcheck not found")
  endif()
endif()

# ────────────────────────────────────────────────────────────────────────────
# Bison detection
# ────────────────────────────────────────────────────────────────────────────
find_package(BISON)
if(BISON_FOUND)
  message(STATUS "Bison found: ${BISON_EXECUTABLE}")
else()
  message(WARNING "Bison not found; some tools may not build")
endif()

# ────────────────────────────────────────────────────────────────────────────
# IPC library
# ────────────────────────────────────────────────────────────────────────────
add_library(ipc STATIC
  src-lib/libipc/ipc.c
)
target_include_directories(ipc PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/include
)
target_compile_options(ipc PRIVATE ${BASE_CFLAGS})

# ────────────────────────────────────────────────────────────────────────────
# POSIX compatibility library
# ────────────────────────────────────────────────────────────────────────────
add_library(posix STATIC
  src-lib/libposix/posix.c
  src-lib/libposix/posix_signal.c
)
target_include_directories(posix PUBLIC
  ${CMAKE_SOURCE_DIR}/src-headers
)
target_compile_options(posix PRIVATE ${BASE_CFLAGS})

# ────────────────────────────────────────────────────────────────────────────
# Kernel stubs
# ────────────────────────────────────────────────────────────────────────────
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
target_compile_options(kern_stubs PRIVATE ${BASE_CFLAGS})

# ────────────────────────────────────────────────────────────────────────────
# Filesystem server
# ────────────────────────────────────────────────────────────────────────────
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
target_compile_options(fs_server PRIVATE ${BASE_CFLAGS})

if(CMAKE_C_COMPILER_ID STREQUAL "Clang")
  # Enable additional SIMD support when building with Clang
  target_compile_options(fs_server PRIVATE
    -msse
    -mavx2
  )
endif()

# ────────────────────────────────────────────────────────────────────────────
# Installation & Subdirectories
# ────────────────────────────────────────────────────────────────────────────
install(FILES
  src-headers/arch.h
  src-headers/ipc.h
  src-headers/libipc.h
  src-headers/posix.h
  src-headers/posix_signal.h
  src-headers/posix_ipc.h
  DESTINATION include
)

# Build userland servers converted from historical Makefiles
add_subdirectory(src-uland/servers/proc_manager)
add_subdirectory(src-uland/servers/reincarnation)
