# Building the 4.4BSD-Lite2 kernel

This short guide explains how to compile the historic 4.4BSD-Lite2 kernel on an i386 host. The steps mirror the classic workflow using `config` and `bmake`. The same procedure works on modern x86_64 systems when passing the appropriate compiler flags.

Before building, run the repository's `setup.sh` script as root to install all
required toolchains and utilities. The script first attempts to install
**bison**, **byacc**, and **bmake** (which includes the full mk framework)
using `apt-get`. If the package installation fails it falls back to `pip` and,
for **bmake**, will download the upstream source and build it locally.
When built from source the script generates a small `.deb` so `dpkg` still
records the package. Optionally **mk-configure** can be installed to provide
an Autotools-style layer on top of `bmake`. All results are logged in
`/tmp/setup.log`. Packages that fail via `apt` are automatically retried with
`pip` when possible.

The script also validates that the `bmake` executable is present and that the
`bmake` package was installed successfully via `dpkg`; it aborts if either
check fails.

If `bison` is missing, install it and rerun `setup.sh`. The script now sets
`YACC="bison -y"` automatically using `/etc/profile.d/yacc.sh`. Then proceed
with the steps below.

1. **Build the `config` utility**
   ```sh
   cd usr/src/usr.sbin/config
   bmake clean && bmake
   ```
   This produces a `config` binary used to generate kernel build directories.

2. **Run `config`**
   ```sh
   cd ../../..
   cd sys/i386/conf
   ../../usr/src/usr.sbin/config/config GENERIC.i386
   ```
   The command creates a compile directory such as `../compile/GENERIC.i386`.

3. **Build the kernel**
   ```sh
   cd ../compile/GENERIC.i386
   bmake depend
   # Append CFLAGS=-m32 for i686 or CFLAGS=-m64 for x86_64
   bmake
   ```
   If successful, the resulting kernel binary (usually `vmunix`) appears in this directory.

If `build.sh` complains about failing to change into the compile directory, ensure that the `config` step ran successfully and that the `../compile/GENERIC.i386` directory exists.

## Building modular components

The microkernel plan extracts portions of `sys/kern` and `sys/dev` into user-space servers or loadable modules.  After building the core kernel you will compile each subsystem separately:

1. Build the core kernel with unwanted drivers disabled.
2. For a user-space server:
   ```sh
   cd servers/<subsystem>
   bmake clean && bmake
   ```
   Install the resulting binary under `/usr/libexec` and configure the boot scripts to start it after the kernel loads.
3. For a loadable module:
   ```sh
   cd modules/<subsystem>
   bmake clean && bmake
   sudo kldload <subsystem>.ko
   ```
4. List the module in `/etc/loader.conf` if it should load automatically at boot.
5. Start user-space servers via init scripts (e.g., `/etc/rc.local`).

The original kernel sources remain under `sys` for historical reference. Place rewritten modules and user-space servers in the new directories so the archived files stay untouched.
These steps keep the historical sources intact while allowing new components to evolve outside the monolithic tree.

## Building the Microkernel Variant

When following the microkernel plan, the minimal kernel resides in
`src-kernel/` and user-space services live under `src-uland/`.  Build them
separately but with the same tools used for the classic kernel:

1. **Compile the microkernel core**
   ```sh
   cd src-kernel
   bmake clean && bmake
   ```
   Use the standard environment variables and append `CFLAGS=-m32` or
   `CFLAGS=-m64` as appropriate.

2. **Build user-space servers and drivers**
   ```sh
   cd src-uland/servers/<name>
   bmake clean && bmake
   ```
   Driver tasks live in `src-uland/drivers/`.  Install each binary under
   `/usr/libexec` and configure startup scripts to launch it early in the boot
   sequence.  See [microkernel_plan.md](microkernel_plan.md) for a description of
   the messaging interfaces used between these components and the microkernel.

## Building the Exokernel Variant

The exokernel layout relocates sources using `tools/organize_sources.sh`. After running the script the kernel sources live in `src-kernel/` and user-level code moves to `src-uland/`. The script finishes with the message `Source tree organization complete.`.

1. **Compile the exokernel**
   ```sh
   cd src-kernel
   bmake clean && bmake
   ```
Use the same environment variables as the classic build. `setup.sh` exports
`YACC=bison -y` for you. If the variable is missing in your shell, export it
before invoking `bmake`. Append `CFLAGS=-m32` or `CFLAGS=-m64` for your
architecture as needed.

2. **Build user-space managers**
   ```sh
   cd src-uland/managers/<name>
   bmake clean && bmake
   ```
   Install each manager under `/usr/libexec` or another appropriate directory.

No additional bmake targets are defined yet; simply run `bmake` in each directory to compile the components.
