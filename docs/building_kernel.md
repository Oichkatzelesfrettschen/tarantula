# Building the 4.4BSD-Lite2 kernel

This short guide explains how to compile the historic 4.4BSD-Lite2 kernel on an i386 host. The steps mirror the classic workflow using `config` and `make`. The same procedure works on modern x86_64 systems when passing the appropriate compiler flags.
If your host lacks `yacc` or `bison`, build the repository's bundled version first:
```sh
cd usr/src/usr.bin/yacc
make clean && make
export YACC=$(pwd)/yacc
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
