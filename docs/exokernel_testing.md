# Booting the Exokernel with Minimal Managers

This guide explains how to start the exokernel with only the essential user-level managers and verify that low-level resource allocation works. It assumes the exokernel and user managers have been built as described in [building_kernel.md](building_kernel.md).

## Requirements

- `qemu-system-i386` or another x86 emulator
- The exokernel binary built under `engine/src-kernel`
- User-level managers (scheduler, memory manager, file server) built under `engine/src-uland`
- A bootable disk image containing the managers in `/bin` or `/usr/bin` (use
  `tools/create_exokernel_image.sh` to generate it)
- The `init` program built under `engine/src-uland/init`

### Creating the Disk Image
Run the helper script after building the kernel and managers:

```sh
tools/create_exokernel_image.sh build/exo.img 64M
```

This produces `build/exo.img`, an ext2 image with the compiled programs in
place. Pass this file to QEMU using `-hda`.

## Booting in QEMU
1. Build a disk image using `tools/create_exokernel_image.sh`.
2. Launch QEMU using the exokernel as the kernel image:
   ```sh
   qemu-system-i386 -kernel path/to/exokernel \
     -hda hdd.img -nographic -serial mon:stdio
   ```
3. QEMU displays the kernel and manager initialization. A minimal boot shows lines similar to:
   ```
   Booting exokernel...
   loading memmgr
   loading sched
   loading fs_mgr
   Managers ready. Launching shell.
   ```

## Verifying Resource Allocation APIs

1. At the shell prompt run the provided allocation test:
   ```sh
   /usr/tests/alloc_test
   ```
2. The program should request a page and an I/O port. Expected output:
   ```
   request_page: success
   request_io_port: success
   ```
3. Check the console or log messages from the managers to confirm that each request reached the corresponding manager and was granted.

If these steps complete without errors the basic resource allocation APIs are functioning under the minimal boot environment.

## Kernel Stub Self-Test

A small program under `tests/` exercises the exokernel stubs without booting the
full system. Build and run it after compiling `libkern_stubs.a`:

```sh
cmake -S engine/src-kernel -B build/kernel -G Ninja
cmake --build build/kernel
cmake -S tests -B build/tests -G Ninja
cmake --build build/tests
./build/tests/test_kern
```

Successful output prints `all ok` and verifies that:

- `kern_open()` delegates to `fs_open()` and opens `README.md`.
- `kern_vm_fault()` returns `true` using the mock VM handler.
- `kern_fork()` creates a child process which exits normally.

## Performance Measurement

Reliable latency numbers require a clean CPU state before each test run. Follow these steps to minimize noise:

1. **Flush caches** – run `clflush` on touched buffers or invalidate the entire L1/L2 caches using a small kernel helper between measurements.
2. **Drop TLB entries** – issue a full TLB shootdown (or toggle CR3) to remove stale address translations.
3. **Pin CPU frequency** – set the governor to `performance` and disable turbo so the core runs at a fixed rate.
4. **Isolate test CPUs** – boot the machine with `isolcpus=` and `nohz_full=` for the cores reserved for measurements. Avoid scheduling other tasks on them.

After collecting at least 30 samples, remove the top and bottom 5% to discard outliers. Compute confidence intervals with bootstrap resampling (10,000 iterations is typical) and report the 95% range.

