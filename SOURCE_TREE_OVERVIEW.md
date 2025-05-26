# Source Tree Overview

This repository contains the 4.4BSD-Lite2 sources as released by the University of California, Berkeley. The following summary lists the major top-level directories and their purpose.

## Top-level directories

- `bin/`, `sbin/`, `usr.bin/`, `usr.sbin/` – user and system utilities
- `lib/`, `libexec/`, `games/`, `share/` – libraries, daemons, games and shared data
- `sys/` – kernel sources
- `src-kernel/` – microkernel stubs and low-level hooks
- `src-uland/` – user-level libraries and servers replacing kernel subsystems
- `src-lib/` – archive libraries moved out of the historical tree
- `src-headers/` – consolidated headers for building user-space managers
- `etc/`, `dev/`, `root/` – system configuration, device files and root account files
- `usr/` – userland programs and manual pages
- `var/` – runtime data
- `ports/` – experimental language ports (Chicken Scheme, Go)
- `Domestic/` and `Foreign/` – cryptographic software separated due to export regulations of the time

The helper script `tools/sync_sys_headers.sh` copies kernel headers from
`usr/src/sys/sys` into `src-headers/sys` and replaces the original directory
with a symlink. This keeps all exported headers under a single location.

## Using this source tree

These directories form the complete 4.4BSD-Lite2 distribution. They can be built using the makefiles provided in the tree or repurposed for porting and reference.
