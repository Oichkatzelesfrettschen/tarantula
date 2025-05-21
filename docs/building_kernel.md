# Building the 4.4BSD-Lite2 kernel

This short guide explains how to compile the historic 4.4BSD-Lite2 kernel on an i386 host. The steps mirror the classic workflow using `config` and `make`. The same procedure works on modern x86_64 systems when passing the appropriate compiler flags.
If your host lacks `yacc` or `bison`, run the helper script which locates or
builds the bundled version automatically:
```sh
export YACC=$(./tools/find_or_build_yacc.sh)
```
Then proceed with the steps below.


1. **Build the `config` utility**
   ```sh
   cd usr/src/usr.sbin/config
   make clean && make
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
   make depend
   # Append CFLAGS=-m32 for i686 or CFLAGS=-m64 for x86_64
   make
   ```
   If successful, the resulting kernel binary (usually `vmunix`) appears in this directory.

If `build.sh` complains about failing to change into the compile directory, ensure that the `config` step ran successfully and that the `../compile/GENERIC.i386` directory exists.

## Building modular components

The microkernel plan extracts portions of `sys/kern` and `sys/dev` into user-space servers or loadable modules.  After building the core kernel you will compile each subsystem separately:

1. Build the core kernel with unwanted drivers disabled.
2. For a user-space server:
   ```sh
   cd servers/<subsystem>
   make clean && make
   ```
   Install the resulting binary under `/usr/libexec` and configure the boot scripts to start it after the kernel loads.
3. For a loadable module:
   ```sh
   cd modules/<subsystem>
   make clean && make
   sudo kldload <subsystem>.ko
   ```

These steps keep the historical sources intact while allowing new components to evolve outside the monolithic tree.
