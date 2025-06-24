````markdown
# Building the 4.4BSD-Lite2 Kernel with a Modern CMake Toolchain

This guide shows how to compile the historic **4.4BSD-Lite2** sources on an **x86_64** (or **i386** with `-m32`) Linux host using **Clang**, **CMake**, and **Ninja**. It assumes you have root privileges to install toolchains and that your repository includes:

- **setup.sh** — installs Clang, Bison, CMake, Ninja, etc., and logs to `/tmp/setup.log`
- **.codex/setup.sh** — CI wrapper (accepts `--offline`)

All helper scripts respect:

- `SRC_ULAND` → user-land sources (default: `src-uland` or `usr/src/usr.sbin/config`)
- `SRC_KERNEL` → kernel sources (default: `src-kernel` or `usr/src/sys/i386`)

---

## Prerequisites

1. **Run the setup script** as root:
   ```bash
   sudo ./setup.sh
````

* Installs **clang**, **bison**, **cmake**, **ninja**, etc.
* If `bison` is missing, install it manually and rerun.
* On CI, use `.codex/setup.sh --offline` for air-gapped environments.

2. **Verify toolchain**:

   ```bash
   clang --version
   bison --version
   cmake --version
   ninja --version
   ```

3. **Set source‐tree env vars** (if you live outside the defaults):

   ```bash
   export SRC_ULAND=${SRC_ULAND:-src-uland}
   export SRC_KERNEL=${SRC_KERNEL:-src-kernel}
   ```

4. **Baseline CPU override**
   By default we compile with:

   ```
   -march=x86-64-v1 -msse2 -mmmx -mfpmath=sse -O3 -fuse-ld=lld
   ```

   To override:

   ```bash
   cmake … -DBASELINE_CPU=x86-64    # or another arch string
   ```

   This controls the `-march=` flag in your CMakeLists.

---

## 1 · Build the `config` Utility

```bash
cmake \
  -S ${SRC_ULAND}/usr.sbin/config \
  -B build/config \
  -G Ninja

cmake --build build/config
```

* Produces `build/config/config`, which generates per‐variant compile directories.

---

## 2 · Generate Kernel Build Directory

```bash
cd ${SRC_KERNEL}/sys/i386/conf
../../build/config/config GENERIC.i386
```

* Creates `../compile/GENERIC.i386` (or a similar variant directory).

---

## 3 · Configure & Build the Kernel

```bash
cmake \
  -S ${SRC_KERNEL}/compile/GENERIC.i386 \
  -B build/kernel \
  -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_STANDARD=23 \
  -DCMAKE_C_FLAGS="-O3 -fuse-ld=lld" \
  -DCMAKE_CXX_FLAGS="-O3 -fuse-ld=lld" \
  -DLLVM_ENABLE_LTO=ON \
  -DBASELINE_CPU=${BASELINE_CPU}

ninja -C build/kernel
```

* **Optional**: add `-DLLVM_ENABLE_POLLY=ON` or post-process with `llvm-bolt` for PGO/POLLY.

---

## 4 · Build User-Space Services

Each service under `${SRC_ULAND}` has its own CMake stanza:

```bash
cmake \
  -S ${SRC_ULAND}/servers/fs \
  -B build/fs \
  -G Ninja

cmake --build build/fs
```

* You can then install with:

  ```bash
  cmake --install build/fs --prefix /usr/libexec
  ```

---

## 5 · Run Kernel Self-Tests

```bash
cmake \
  -S tests \
  -B build/tests \
  -G Ninja

cmake --build build/tests

./build/tests/test_kern    # should print “all ok”
```

---

## 6 · Legacy Makefile Support

If you prefer the classic Make in `tests/`:

1. **Build the static libs** first:

   ```bash
   cmake -S . -B build -G Ninja
   cmake --build build --target ipc posix kern_stubs
   ```
2. **Run the Makefile**:

   ```bash
   make -C tests
   ```

---

## 7 · Cleaning Up

Before committing, purge all generated artifacts:

```bash
rm -rf build/                                    # CMake/Ninja outputs
rm -rf ${SRC_KERNEL}/sys/i386/compile/*          # variant compile dirs
git clean -fdx                                   # double-check nothing left
```

Keeping the tree free of build outputs prevents merge conflicts and keeps patches concise.
