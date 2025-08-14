````markdown
# Building the 4.4BSD-Lite2 Kernel

This guide shows how to compile the historic **4.4BSD-Lite2** sources on an **x86_64** (or **i386** with `-m32`) Linux host using **Clang**, **CMake**, and **Ninja**. It assumes you have root privileges to install toolchains and that your repo includes:

- `docs/setup_guide.md`       – outlines required packages and environment variables
- `tools/check_build_env.sh`  – verifies presence of build tools like `clang` and `bison`

All helper scripts respect:

```bash
export SRC_ULAND=${SRC_ULAND:-src-uland}    # user-land sources
export SRC_KERNEL=${SRC_KERNEL:-src-kernel} # kernel sources
````

---

## 1 · Install & Verify Dependencies

1. **Install the toolchain** using your system package manager:

   ```bash
   sudo apt update
   sudo apt install -y \
     build-essential cmake ninja-build \
     clang lld lldb llvm \
     bison flex \
     bear ccache gdb ripgrep \
     clang-format clang-tidy pre-commit
   ```
2. **Verify** required tools:

   ```bash
   command -v clang
   command -v bison
   command -v cmake
   command -v ninja
   ```

---

## 2 · Baseline CPU & Linker Flags

By default we target **x86-64** with SSE2/MMX and LLVM’s `lld`.  To set this globally, pass:

```bash
-DCMAKE_C_FLAGS="-O3 -fuse-ld=lld -march=x86-64 -msse2 -mmmx -mfpmath=sse" \
-DCMAKE_CXX_FLAGS="-O3 -fuse-ld=lld -march=x86-64 -msse2 -mmmx -mfpmath=sse"
```

If you need a different microarchitecture, override with:

```bash
-DBASELINE_CPU=<your-arch>
```

---

## 3 · Build the `config` Utility

The first step is to compile the `config` tool that generates per-kernel build directories:

```bash
cmake \
  -S "${SRC_ULAND}/usr.sbin/config" \
  -B build/config \
  -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_STANDARD=23 \
  -DCMAKE_C_FLAGS="-O3 -march=${BASELINE_CPU} -fuse-ld=lld" \
  -DCMAKE_CXX_FLAGS="-O3 -march=${BASELINE_CPU} -fuse-ld=lld"
cmake --build build/config
```

This produces `build/config/config`.

---

## 4 · Generate the Kernel Build Directory

Run `config` from your kernel source tree:

```bash
cd "${SRC_KERNEL}/sys/i386/conf"
../../build/config/config GENERIC.i386
```

That creates a kernel build tree under:

```
${SRC_KERNEL}/sys/i386/compile/GENERIC.i386
```

---

## 5 · Configure & Build the Kernel

Change into the generated directory and invoke CMake/Ninja:

```bash
cmake \
  -S "${SRC_KERNEL}/sys/i386/compile/GENERIC.i386" \
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

> **Alternate “no-AVX” profile**
> If you need to disable AVX on older hardware, add `-mno-avx` (and optionally `-msse`):
>
> ```bash
> -DCMAKE_C_FLAGS="-O3 -fuse-ld=lld -march=x86-64 -msse -mno-avx"
> ```

> **Optional optimizations**
>
> * Enable Polly: `-DLLVM_ENABLE_POLLY=ON`
> * Post-process with LLVM-Bolt for PGO: build as above, then
>
>   ```bash
>   llvm-bolt build/kernel/GENERIC.i386 -o GENERIC.i386.bolted
>   ```

---

## 6 · Build User-Space Services

Each server under `${SRC_ULAND}` has its own CMake build. For example, the filesystem server:

```bash
cmake \
  -S "${SRC_ULAND}/servers/fs" \
  -B build/fs \
  -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_STANDARD=23 \
  -DCMAKE_C_FLAGS="-O3 -fuse-ld=lld -march=${BASELINE_CPU} -msse2 -mmmx -mfpmath=sse"
cmake --build build/fs
```

Install into your staging prefix (e.g. `/usr/libexec`):

```bash
cmake --install build/fs --prefix /usr/libexec
```

Repeat for other services (e.g. `proc_manager`, `reincarnation`, etc.).

---

## 7 · Run Kernel Self-Tests

```bash
cmake \
  -S tests \
  -B build/tests \
  -G Ninja \
  -DCMAKE_C_STANDARD=23 \
  -DCMAKE_C_FLAGS="-O3 -march=${BASELINE_CPU}"
cmake --build build/tests
./build/tests/test_kern   # should print "all ok"
```

---

## 8 · Legacy Makefile Support

If you need to invoke the original Makefiles in `tests/`:

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
rm -rf "${SRC_KERNEL}/sys/i386/compile/"*   # per-kernel dirs
git clean -fdx                              # purge untracked files
```

Keeping your tree free of build outputs prevents merge conflicts and keeps patches concise.
