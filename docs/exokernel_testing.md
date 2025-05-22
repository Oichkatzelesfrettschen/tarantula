# Booting the Exokernel with Minimal Managers

This guide explains how to start the exokernel with only the essential user-level managers and verify that low-level resource allocation works. It assumes the exokernel and user managers have been built as described in [building_kernel.md](building_kernel.md).

## Requirements

- `qemu-system-i386` or another x86 emulator
- The exokernel binary built under `src-kernel`
- User-level managers (scheduler, memory manager, file server) built under `src-uland`
- A bootable disk image containing the managers in `/bin` or `/usr/bin`
- The `init` program built under `src-uland/init`

## Booting in QEMU
1. Create a disk image with the managers installed and copy `init` to `/sbin/init`.
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
cd src-kernel && bmake
cd ../tests && bmake clean all
./test_kern
```

Successful output prints `all ok` and verifies that:

- `kern_open()` delegates to `fs_open()` and opens `README.md`.
- `kern_vm_fault()` returns `true` using the mock VM handler.
- `kern_fork()` creates a child process which exits normally.
