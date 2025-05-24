# Userland Servers and Libraries

This directory holds user-space replacements for kernel functionality.
Files are copied from the historical `sys/` tree. Keep comments noting their origins.
`libkern_sched` and `libvm` now live under `src-lib/` with compatibility
makefiles in this directory. Build them via these wrappers or directly in
`src-lib`.
Use the provided makefiles to build the `fs_server` program as well.
