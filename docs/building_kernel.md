# Building the 4.4BSD-Lite2 kernel

This guide explains how to build the historic 4.4BSD-Lite2 sources with a modern
CMake toolchain.  The commands assume an x86_64 host but work on i386 when using
`-m32` flags.

Before building, run the repository's `setup.sh` script as root to install all required toolchains. Codex CI calls `.codex/setup.sh`, which passes `--offline` when needed. The script installs **clang**, **bison**, `cmake` and related packages, logging to `/tmp/setup.log`.

If `bison` is missing, install it and rerun `setup.sh`. The script now sets
`YACC="bison -y"` automatically using `/etc/profile.d/yacc.sh`.
Before continuing, verify `bison` is available by running:
```sh
command -v bison
```
Then proceed with the steps below.

The repository also includes a simple **CMake** build. After installing the
dependencies you can configure the entire tree using Ninja:

Before building, ensure the root script `setup.sh` is run as as root to configure the environment.  The script installs all required
packages using `apt-get update && apt-get dist-upgrade` followed by
installation of **clang**, **bison**, **cmake** and **ninja**.  Packages that are
missing from `apt` are retried with `pip` or `npm`.  When invoked via
`.codex/setup.sh` the wrapper passes `--offline` if the network is unreachable.

All helper scripts expect the environment variables `SRC_ULAND` and
`SRC_KERNEL` to point to the userland and kernel source directories.  They
default to `src-uland` and `src-kernel`.
=
## 1. Build the `config` utility
```sh
cmake -S ${SRC_ULAND:-usr/src}/usr.sbin/config -B build/config -G Ninja
cmake --build build/config
```
The resulting binary generates kernel build directories.

## 2. Run `config`
```sh
cd sys/i386/conf
../../build/config/config GENERIC.i386
```
This creates a directory such as `../compile/GENERIC.i386`.

## 3. Configure and build the kernel
```sh
cmake -S ../compile/GENERIC.i386 -B build/kernel -G Ninja \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_STANDARD=23 -DCMAKE_C_FLAGS='-O3' \
      -DLLVM_ENABLE_LTO=ON
ninja -C build/kernel
```
Optional Polly and BOLT optimizations can be enabled by passing
`-DLLVM_ENABLE_POLLY=ON` and post-processing the binary with `llvm-bolt`.

## Building user-space components
The microkernel and exokernel plans compile user-space services under
`src-uland/`.  Configure each directory with CMake and build with Ninja:
```sh
cmake -S src-uland/servers/fs -B build/fs -G Ninja
cmake --build build/fs
```
Install the resulting binaries under `/usr/libexec` or another suitable
location.

## Running Kernel Self-Tests
A small program under `tests/` exercises the kernel stubs without booting the
system:
```sh
cmake -S tests -B build/tests -G Ninja
cmake --build build/tests
./build/tests/test_kern
```
It prints `all ok` when the stubs behave correctly.
