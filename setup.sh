````markdown
# Setup Script Guide

This document describes the `setup.sh` helper, which bootstraps your build and development environment by installing core, language, and cross-compiler toolchains. All output is logged to `/tmp/setup.log`; failures are recorded but do not abort the entire process, and missing URLs are noted in `README.md` with Markdown strikethrough.

---

## Invocation & Flags

```bash
./setup.sh [--offline] [--core] [--langs] [--cross] [--all]
````

* `--offline`
  Assume no network access; installs only from locally cached `.deb` or pip wheels.
* `--core`
  Install core build tools (compilers, linkers, formatters, analysis utilities).
* `--langs`
  Install language runtimes (Go, Rust, Python, Haskell, Java, etc.).
* `--cross`
  Install cross-compilers for multiple architectures.
* `--all`
  Equivalent to `--core --langs --cross`.

If none of `--core`, `--langs`, or `--cross` are specified, the script defaults to `--all`.

---

## Logging & Fail-Fast

* **Trace & fail-fast**: `set -x; set -u -o pipefail`
* **Log file**: `/tmp/setup.log`
* **On any command failure**: appends `FAILED cmd: …` to the log, continues execution
* **Timestamps**: each log entry is prefixed with an ISO 8601 timestamp

---

## Environment & Caches

* **APT cache dir**: `$(dirname "$0")/third_party/apt`
* **PIP cache dir**: `third_party/pip`
* **Offline packages**: `offline_packages/`
* **README.md URL notes**: unreachable URLs are appended with `~~URL~~`

---

## Installation Phases

### 1. Preflight & Offline Detection

* Checks `apt-get update`; if that fails, flips to `OFFLINE_MODE=1`.
* Ensures `$DEBIAN_FRONTEND=noninteractive`.
* Traps `ERR` to record failures without exiting.

### 2. Core Packages (`--core`)

Enables foreign architectures, updates APT, then installs:

```text
build-essential, gcc, g++, clang, lld, llvm,
clang-format, clang-tidy, uncrustify, astyle, editorconfig, pre-commit,
shellcheck, codespell,
make, ninja-build, cmake, meson,
autoconf, automake, libtool, m4, gawk, flex, bison, byacc,
pkg-config, file, ca-certificates, curl, git, unzip,
libopenblas-dev, liblapack-dev, libeigen3-dev,
libbsd0, libbsd-dev,
strace, ltrace, linux-perf, systemtap, crash,
valgrind, kcachegrind, trace-cmd, kernelshark,
llvm-polly, llvm-bolt,
libasan6, libubsan1, likwid, hwloc,
graphviz, doxygen, python3-sphinx, cloc, cscope, cflow, plantuml
```

Plus Python ML/Ops libs:

```text
python3, python3-pip, python3-dev, venv, wheel,
numpy, scipy, pandas, matplotlib, scikit-learn,
torch, torchvision, torchaudio, onnx, onnxruntime
```

And miscellaneous CLI tools (e.g. QEMU, GUI toolkits, container runtimes, formal methods).

### 3. Language Runtimes (`--langs`)

Installs via APT/pip/npm:

```text
golang-go, nodejs, npm, typescript,
rustc, cargo, clippy, rustfmt,
lua5.4, luarocks,
ghc, cabal-install, hlint, stylish-haskell,
sbcl, ecl, clisp, slime,
ldc, gdc, dmd, dub,
chicken, openjdk-17-jdk, maven, gradle, dotnet-sdk-8, mono-complete,
swift, kotlin, ruby, php-cli, composer, r-base, dart, flutter, gnat, gfortran, cobol, fpc, zig, nim, crystal, gforth
```

### 4. Cross-Compilers (`--cross`)

Installs cross-toolchains for:

```text
ia64, i686, aarch64, arm, riscv64, powerpc, m68k, hppa, loongarch, mips, etc.
```

Also fetches and unpacks `ia16-elf-gcc` from GitHub releases.

---

## Fallback & Retry

* **`apt_pin_install`**: attempts to install from local `.deb` cache, then APT by exact version.
* **`install_with_pip`**: uses pip3 and caches wheels/tars.
* **`npm_install`**: uses `npm -g`.
* **`retry_failures`**: after the main pass, retries any APT, pip, or npm failures.

---

## Protobuf Compiler

Installs a pinned `protoc`:

```bash
PROTO_VERSION=25.1
PROTO_URL="https://.../protoc-${PROTO_VERSION}-linux-x86_64.zip"
curl_head_check "$PROTO_URL"
unzip to /usr/local; cache failures
```

---

## Finalization

* Creates `/etc/profile.d/yacc.sh` to export `YACC="bison -y"`.
* Symlinks `yacc` to `bison` in `/usr/local/bin`.
* Cleans up APT lists: `apt-get clean && rm -rf /var/lib/apt/lists/*`.
* Logs any remaining failures at the end of `/tmp/setup.log`.

---

## Full Usage Example

```bash
# Install everything, online:
sudo ./setup.sh

# Install only core and languages, offline:
sudo ./setup.sh --offline --core --langs
```

Check `/tmp/setup.log` for detailed success/failure records.
