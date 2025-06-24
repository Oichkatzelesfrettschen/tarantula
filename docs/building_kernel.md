# Building the 4.4BSD-Lite2 Kernel

This guide shows how to compile the historic **4.4BSD-Lite2** sources on an **x86_64** (or **i386** with `-m32`) Linux host using **Clang**, **CMake**, and **Ninja**. It assumes you have root privileges to install toolchains and that your repo includes:

- `setup.sh`                  – installs clang, bison, cmake, ninja, etc. (logs to `/tmp/setup.log`)  
- `.codex/setup.sh`           – CI wrapper (accepts `--offline`)  
- `tools/check_build_env.sh`  – enforces `$YACC="bison -y"`  

All helper scripts respect:

```bash
export SRC_ULAND=${SRC_ULAND:-src-uland}   # user-land sources
export SRC_KERNEL=${SRC_KERNEL:-src-kernel} # kernel sources
```

---

## 1 · Install & Verify Dependencies

1. **Run the setup script** as root:
   ```bash
   sudo ./setup.sh
   ```
   Or in CI environments:
   ```bash
   ./.codex/setup.sh --offline
   ```
2. **Ensure** `$YACC` is correct for legacy Makefiles:
   ```bash
   source /etc/profile.d/yacc.sh       # sets YACC="bison -y"
   tools/check_build_env.sh            # validates YACC value
   ```
3. **Verify** required tools:
   ```bash
   command -v clang
   command -v bison
   command -v cmake
   command -v ninja
   ```

---

## 2 · Baseline CPU & Linker Flags

By default we target **x86-64-v1** with SSE2/MMX and LLVM’s `lld`:

```
-DCMAKE_C_FLAGS="-O3 -fuse-ld=lld -march=x86-64-v1 -msse2 -mmmx -mfpmath=sse"
-DCMAKE_CXX_FLAGS="-O3 -fuse-ld=lld -march=x86-64-v1 -msse2 -mmmx -mfpmath=sse"
```

To override the `-march=` target:

```bash
-DBASELINE_CPU=<your-arch>  
```

---

## 3 · Build the `config` Utility

```bash
cmake \
  -S "${SRC_ULAND}/usr.sbin/config" \
  -B build/config \
  -G Ninja
cmake --build build/config
```

Produces `build/config/config`, which generates per-variant kernel build trees.

---

## 4 · Generate the Kernel Build Directory

```bash
cd "${SRC_KERNEL}/sys/i386/conf"
../../build/config/config GENERIC.i386
```

Creates `../compile/GENERIC.i386` containing all `Makefile` fragments.

---

## 5 · Configure & Build the Kernel

```bash
cmake \
  -S "${SRC_KERNEL}/compile/GENERIC.i386" \
  -B build/kernel \
  -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_STANDARD=23 \
  -DCMAKE_C_FLAGS="-O3 -fuse-ld=lld -march=${BASELINE_CPU} -msse2 -mmmx -mfpmath=sse" \
  -DCMAKE_CXX_FLAGS="-O3 -fuse-ld=lld -march=${BASELINE_CPU} -msse2 -mmmx -mfpmath=sse" \
  -DLLVM_ENABLE_LTO=ON \
  -DBASELINE_CPU="${BASELINE_CPU}"
ninja -C build/kernel
```

> **Optional:**  
> • Enable Polly: `-DLLVM_ENABLE_POLLY=ON`  
> • Post-process with `llvm-bolt` for further PGO/BOLT optimizations  

---

## 6 · Build User-Space Services

Each service under `${SRC_ULAND}` has its own CMake directory:

```bash
cmake \
  -S "${SRC_ULAND}/servers/fs" \
  -B build/fs \
  -G Ninja
cmake --build build/fs
```

Install to `/usr/libexec` or another prefix:

```bash
cmake --install build/fs --prefix /usr/libexec
```

---

## 7 · Run Kernel Self-Tests

```bash
cmake \
  -S tests \
  -B build/tests \
  -G Ninja
cmake --build build/tests
./build/tests/test_kern   # should print "all ok"
```

---

## 8 · Legacy Makefile Support

If you prefer the classic Makefiles in `tests/`:

```bash
cmake -S . -B build -G Ninja
cmake --build build --target ipc posix kern_stubs
make -C tests
```

---

## 9 · Cleaning Up

Before committing, remove all generated artifacts:

```bash
rm -rf build/                               # CMake/Ninja outputs
rm -rf "${SRC_KERNEL}/sys/i386/compile/"*   # per-variant dirs
git clean -fdx                              # purge untracked files
```

Keeping the tree free of build outputs prevents merge conflicts and keeps patches concise.  
