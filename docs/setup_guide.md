# Environment Provisioning and Tooling

This guide documents how to provision a development host for the Tarantula tree. The former `setup.sh` script has been replaced by the following manual steps.

## 1 · Install toolchain and analysis utilities

Update the package index and install the required packages:

```bash
sudo apt update
sudo apt install -y \
  build-essential cmake ninja-build meson \
  clang lld lldb llvm \
  bison flex \
  bear ccache gdb ripgrep \
  clang-format clang-tidy pre-commit
```

| Tool                     | Purpose                                                         |
|--------------------------|-----------------------------------------------------------------|
| `clang`, `lld`, `lldb`, `llvm` | LLVM-based compiler, linker and debugger suite                 |
| `bison`, `flex` | Parser and lexer generators used by legacy build scripts       |
| `cmake`, `ninja-build`, `meson`   | Configure and drive modern build systems                      |
| `bear`                   | Generate `compile_commands.json` for `clang-tidy` and `clangd`  |
| `ccache`                 | Cache object files to speed up repeated builds                  |
| `gdb`, `lldb`            | Native and LLVM debuggers                                       |
| `ripgrep`                | Fast source tree searching                                      |
| `clang-format`, `clang-tidy` | Code formatting and static analysis                         |
| `pre-commit`             | Manage git hooks and linting                                   |

After provisioning, verify the toolchain:

```bash
tools/check_build_env.sh
```

### Additional analysis and instrumentation tools

The repository benefits from a wider catalogue of linters, profilers and
duplicate‑code detectors.  The table below summarizes primary installation
avenues drawn from their authoritative sources—Debian `apt` for packaged
utilities, Python's `pip` for PyPI projects, Node's `npm` registry for
JavaScript tools, and source builds when no distribution package exists.

| Tool       | Installation Method | Example Command                                                                 |
|------------|---------------------|---------------------------------------------------------------------------------|
| lizard     | pip                  | `pip install lizard`                                                           |
| cloc       | apt                  | `sudo apt install cloc`                                                        |
| cscope     | apt                  | `sudo apt install cscope`                                                      |
| diffoscope | pip                  | `pip install diffoscope`                                                       |
| dtrace     | source build        | `git clone https://github.com/dtrace4linux/linux.git && cd linux && make && sudo make install` |
| valgrind   | apt                  | `sudo apt install valgrind`                                                    |
| cppcheck   | apt                  | `sudo apt install cppcheck`                                                    |
| sloccount  | apt                  | `sudo apt install sloccount`                                                   |
| flawfinder | apt                  | `sudo apt install flawfinder`                                                  |
| gdb        | apt                  | `sudo apt install gdb`                                                         |
| pylint     | pip                  | `pip install pylint`                                                           |
| flake8     | pip                  | `pip install flake8`                                                           |
| mypy       | pip                  | `pip install mypy`                                                             |
| semgrep    | pip                  | `pip install semgrep`                                                          |
| eslint     | npm                  | `npm install -g eslint`                                                        |
| jshint     | npm                  | `npm install -g jshint`                                                        |
| jscpd      | npm                  | `npm install -g jscpd`                                                         |
| nyc        | npm                  | `npm install -g nyc`                                                           |

For configuration details see [tool_config.md](tool_config.md). Sample outputs from each utility are captured in [tool_reports.md](tool_reports.md).

## 2 · Helper scripts in `tools/`

The `tools/` directory contains utilities that complement the build environment:

- `check_build_env.sh` – confirms required build tools like `meson` and `bison`.
- `build_collect_warnings.sh` – compiles sources and aggregates compiler warnings.
- `generate_compiledb.sh` – emits a `compile_commands.json` database.
- `run_clang_tidy.sh` – runs `clang-tidy` across the tree using the database.
- `generate_cscope.sh` / `generate_ctags.sh` – create code navigation indexes.
- `create_exokernel_image.sh` – assembles a bootable disk image.
- `post_fhs_cleanup.sh`, `migrate_to_fhs.sh`, `migrate_to_src_layout.sh`, and `organize_sources.sh` – migration helpers.

Invoke each script with `--help` when available for additional options.

## 3 · Building the kernel

Once the environment is prepared, follow [`docs/building_kernel.md`](building_kernel.md) to configure and compile the 4.4BSD‑Lite2 kernel and user‑space services. The document covers baseline compiler flags, generating configuration headers, and running the self‑tests.

Keeping these steps in Markdown ensures the setup process remains accessible and version‑controlled, replacing ad‑hoc shell scripts with reproducible documentation.
