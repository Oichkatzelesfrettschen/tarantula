# Debugging the Build Environment

This note captures the results of running `setup.sh` in a minimal container
without network access. The script failed to install many packages, leaving
several build tools missing. The `/tmp/setup.log` file showed `APT FAIL` and
`PIP FAIL` entries for the following programs:

- `aptitude` and the **clang/llvm** toolchain
- `cmake` and `ninja`
- `bison`, `byacc`, `flex`
- `meson`, `autoconf`, `automake`, `libtool`, `m4`
- `uncrustify`, `astyle`, `editorconfig`, `pre-commit`
- math libraries such as `libopenblas-dev`, `liblapack-dev`, `libeigen3-dev`
- various tracing tools (`strace`, `ltrace`, `linux-perf`, `systemtap`)

Only `gcc`, `g++`, `make`, `ninja` and `cmake` were present.

To quickly verify which tools are available, run:

```sh
./tools/check_build_env.sh
```

It prints a list of missing commands and exits non-zero if any are absent.
Populate `third_party/apt` and `third_party/pip` with the corresponding
packages while online to allow `setup.sh` to succeed offline.
