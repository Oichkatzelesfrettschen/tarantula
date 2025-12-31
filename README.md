# BSD/Tarantula: A Modern Microkernelization Attempt of 4.4BSD-Lite2: The Final Unix from Berkeley. 

BSD/Tarantula modernizes the historic 4.4BSD-Lite2 codebase by carving out a
minimal microkernel that retains only scheduling, memory and IPC hooks. Device
drivers, filesystems and networking stacks migrate into user-space servers to
exercise a modular architecture. An accompanying exokernel track goes further
by exposing hardware resources through a thin protection layer so libraries can
implement their own policies. See
[docs/microkernel_plan.md](docs/microkernel_plan.md) and
[docs/microkernel_functional_model.md](docs/microkernel_functional_model.md)
for microkernel details, and
[docs/exokernel_plan.md](docs/exokernel_plan.md) for the exokernel roadmap.

# Environment provisioning
Install prerequisites using the commands in
[docs/setup_guide.md](docs/setup_guide.md). The guide replaces the former
`setup.sh` script and enumerates every tool required to build and analyze the
tree.
For per-tool configuration guidance see [docs/tool_config.md](docs/tool_config.md); sample outputs appear in [docs/tool_reports.md](docs/tool_reports.md).

# 4.4BSD-Lite2, the last Unix from Berkeley

The story: https://en.wikipedia.org/wiki/History_of_the_Berkeley_Software_Distribution#4.4BSD_and_descendants

Downloaded from: ftp://alge.anart.no/pub/BSD/4.4BSD-Lite/4.4BSD-Lite2.tar.gz

For kernel build instructions see [docs/building_kernel.md](docs/building_kernel.md).
Install the toolchain using the commands in
[docs/setup_guide.md](docs/setup_guide.md). After provisioning, set up the
repository's git hooks with `pre-commit install --install-hooks` as described in
[docs/precommit.md](docs/precommit.md).
The tree also ships a minimal **CMake** configuration.  Generate Ninja files
with:

```sh
cmake -S . -B build -G Ninja
cmake --build build
```
`find_package(BISON)` checks that **bison** is available.  See
[docs/cmake_upgrade.md](docs/cmake_upgrade.md) for a gradual migration guide
from the historic `bmake` system to CMake.  The top-level build enables the
C23 language standard and defaults to `-O3`.  It prefers **clang** when no
compiler is specified but honors any toolchain supplied via
`-DCMAKE_C_COMPILER`.  All configurations request the LLVM linker via
`-fuse-ld=lld`; when compiling with Clang and leaving `ENABLE_NATIVE_OPT`
enabled, the baseline flags expand to
`-march=<BASELINE_CPU> -msse2 -mmmx -mfpmath=sse -O3`.  Toggle the behavior
with `-DENABLE_NATIVE_OPT=OFF`, adjust `BASELINE_CPU` (default: `x86-64`), or
pass explicit `CMAKE_C_FLAGS` when different tuning is required.
For offline work, pre-download `.deb` packages into `third_party/apt` and Python
wheels into `third_party/pip` using `apt-get download <pkg>` and `pip download
<pkg>`. Copy those archives into `offline_packages/` and install them with
`dpkg -i` when the network is unavailable. You can verify which commands are
available at any time by running `tools/check_build_env.sh`; it lists missing
tools and exits non-zero when any are absent.

## Running Tests

Ensure the prerequisites from [docs/setup_guide.md](docs/setup_guide.md) are available before compiling the tests.

Using the historical Makefile builds four standalone programs:

```sh
make -C tests          # test_kern, spinlock_cpp, mailbox_test, fifo_test
```

An experimental CMake flow is also provided:

```sh
cmake -S tests -B build/tests -G Ninja
cmake --build build/tests
```

Execute the resulting binaries directly, for example:

```sh
./tests/test_kern      # prints "all ok"
```

See [docs/building_kernel.md](docs/building_kernel.md) for a more detailed walkthrough.

For FHS migration steps see [docs/fhs_migration.md](docs/fhs_migration.md).
For microkernel tasks see [docs/microkernel_plan.md](docs/microkernel_plan.md)
and the functional overview in
[docs/microkernel_functional_model.md](docs/microkernel_functional_model.md).
For exokernel tasks see [docs/exokernel_plan.md](docs/exokernel_plan.md).
The mailbox-based IPC API is described in [docs/IPC.md](docs/IPC.md) and
provides `ipc_queue_init()`, `ipc_queue_send()`/`recv()` and blocking
variants for message passing.

### User's Supplementary Documents
* An Introduction to the C shell: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/04.csh.pdf?raw=true
* Mail Reference Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/07.mail.pdf?raw=true
* The RAND MH Message Handling System: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/08.mh.pdf?raw=true
* An Introduction to Display Editing with Vi: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/11.vitut.pdf?raw=true
* Ex Reference Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/12.exref.pdf?raw=true
* Ex/Vi Reference Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/13.viref.pdf?raw=true
* JOVE Manual for UNIX Users: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/14.jove.pdf?raw=true
* A Revised Version of -ms: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/18.msdiffs.pdf?raw=true
* Writing Papers with NROFF using −me: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/19.memacros.pdf?raw=true
* -me Reference Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/20.meref.pdf?raw=true
* BIB - A Program for Formatting Bibliographies: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/28.bib.pdf?raw=true
* A Guide to the Dungeons of Doom: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/30.rogue.pdf?raw=true
* Star Trek: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/usd/31.trek.pdf?raw=true

### Programmer's Supplementary Documents
* Berkeley Software Architecture Manual, 4.4BSD Edition: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/05.sysman.pdf?raw=true
* Berkeley Pascal User’s Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/07.pascal.pdf?raw=true
* Debugging with GDB: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/10.gdb.pdf?raw=true
* RCS - A System for Version Control: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/13.rcs.pdf?raw=true
* An Introduction to the Source Code Control System: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/14.sccs.pdf?raw=true
* gprof: a Call Graph Execution Profiler: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/18.gprof.pdf?raw=true
* Screen Updating and Cursor Movement Optimization: A Library Package: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/19.curses.pdf?raw=true
* An Introductory 4.4BSD Interprocess Communication Tutorial: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/20.ipctut.pdf?raw=true
* An Advanced 4.4BSD Interprocess Communication Tutorial: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/psd/21.ipc.pdf?raw=true

### System Manager's Manuals
* Installing and Operating 4.4BSD UNIX: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/01.setup.pdf?raw=true
* Building Kernels with Config: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/02.config.pdf?raw=true
* Fsck - The UNIX File System Check Program: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/03.fsck.pdf?raw=true
* Disc Quotas in a UNIX Environment: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/04.quotas.pdf?raw=true
* A Fast File System for UNIX: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/05.fastfs.pdf?raw=true
* The 4.4BSD NFS Implementation: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/06.nfs.pdf?raw=true
* Line Printer Spooler Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/07.lpd.pdf?raw=true
* SENDMAIL Installation And Operation Guide: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/08.sendmailop.pdf?raw=true
* SENDMAIL - An Internetwork Mail Router: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/09.sendmail.pdf?raw=true
* Name Server Operations Guide for BIND: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/10.named.pdf?raw=true
* Timed Installation and Operation Guide: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/11.timedop.pdf?raw=true
* The Berkeley UNIX Time Synchronization Protocol: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/12.timed.pdf?raw=true
* Amd, The Automounter Reference Manual: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/13.amd.pdf?raw=true
* Networking Implementation Notes: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/18.net.pdf?raw=true
* The PERL Programming Language: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/share/doc/smm/19.perl.pdf?raw=true

### Others
* A New Hashing Package for UNIX: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/src/lib/libc/db/doc/hash.usenix.pdf?raw=true
* LIBTP: Portable, Modular Transactions for UNIX: https://github.com/sergev/4.4BSD-Lite2/blob/master/usr/src/lib/libc/db/doc/libtp.usenix.pdf?raw=true

## Tools

The `tools` directory contains helper scripts. `generate_dependency_graph.py` scans the source tree to build a DOT file of include dependencies and syscall implementations. Run `python3 tools/generate_dependency_graph.py` to produce `docs/dependency_graph.dot`. Use `--include-prefix` to add header search prefixes or `--ignore-unresolved-includes` to drop missing headers. Pass `--include-calls` to add a simple call graph. The `docs/dependency_graph.dot` file tracked in this repository was generated using this command and can be regenerated at any time with `python3 tools/generate_dependency_graph.py`.
All Python utilities require **Python 3**.
`tools/generate_compiledb.sh` runs `compiledb` to create a `compile_commands.json` database for clang-tidy.

## Spinlock options

The header `src-headers/spinlock.h` exposes two compile-time switches:

* `CONFIG_SMP` — set to `0` to disable spinlocks on uniprocessor builds.
* `USE_TICKET_LOCK` — set to `1` to use the FIFO ticket lock variant.

When using CMake simply pass the defines via `CFLAGS` when configuring:

```sh
cmake -S . -B build -G Ninja -DCMAKE_C_FLAGS="-DCONFIG_SMP=0"
ninja -C build
```

