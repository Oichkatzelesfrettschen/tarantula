# AGENTS File Overview

This repository uses `AGENTS.md` files to document guidelines in
specific directories. Below is a short summary of each file.

- **AGENTS.md** – repository overview and workflow expectations.
  Keep commits focused, update docs when relevant and try building
  using `docs/building_kernel.md` for code changes.
- **docs/AGENTS.md** – describes the documentation folder; no tests
  are required when editing docs.
- **.github/AGENTS.md** – notes that CI YAML files were removed and
  builds rely solely on clang with the C23 standard.
- **dev/AGENTS.md** – historical device scripts; no automated tests.
- **etc/AGENTS.md** – sample system configuration files for reference.
- **root/AGENTS.md** – placeholder representing the root user's home.
- **src-headers/AGENTS.md** – copied header files for building
  user-space servers.
- **src-kernel/AGENTS.md** – microkernel stubs compiled into
  `libkern_stubs.a` via a local makefile.
- **src-uland/AGENTS.md** – user-space replacements for kernel
  components with compatibility makefiles.
- **src-uland/servers/AGENTS.md** – build each server using its local
  Makefile.
- **third_party/AGENTS.md** – caches archives used during offline
  environment provisioning.
- **tools/AGENTS.md** – helper scripts; no tests required to modify
  them.
- **usr/AGENTS.md** – classic userland tree built with historical
  makefiles.
- **usr/src/AGENTS.md** – mirrors the original `src` hierarchy including
  kernel sources under `sys/`.
- **usr/src/sys/AGENTS.md** – kernel sources; follow existing style and
  see `docs/building_kernel.md` for build steps.
- **Domestic/AGENTS.md** – domestic userland including cryptographic
  software; preserve original paths.
- **Foreign/AGENTS.md** – non-crypto version of the userland.
- **var/AGENTS.md** – runtime data layout, rarely changed.
