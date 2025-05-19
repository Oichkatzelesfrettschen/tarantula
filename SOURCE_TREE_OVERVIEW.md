# Source Tree Overview

This repository contains the 4.4BSD-Lite2 sources as released by the University of California, Berkeley. The following summary lists the major top-level directories and their purpose.

## Top-level directories

- `bin/`, `sbin/`, `usr.bin/`, `usr.sbin/` – user and system utilities
- `lib/`, `libexec/`, `games/`, `share/` – libraries, daemons, games and shared data
- `sys/` – kernel sources
- `src-kernel/` – microkernel stubs and low-level hooks
- `src-uland/` – user-level libraries and servers replacing kernel subsystems
- `etc/`, `dev/`, `root/` – system configuration, device files and root account files
- `usr/` – userland programs and manual pages
- `var/` – runtime data
- `Domestic/` and `Foreign/` – cryptographic software separated due to export regulations of the time

## Using this source tree

These directories form the complete 4.4BSD-Lite2 distribution. They can be built using the makefiles provided in the tree or repurposed for porting and reference.
