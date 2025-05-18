# FHS Migration Guide

This document expands on the tasks in [reorg_plan.md](reorg_plan.md) to show how
the historical 4.4BSD-Lite2 layout maps onto a modern Filesystem Hierarchy
Standard (FHS) structure.

## Background

`reorg_plan.md` lists generating an inventory, drafting new makefiles and
restructuring directories as key steps. After cataloging files the next phase is
to place them under directories that match the FHS while retaining references to
the original locations.

## Example directory mappings

- `/usr/adm` &rarr; `/var/log` – system logs and accounting data
- `/usr/spool` &rarr; `/var/spool` – generic spool directories
- `/usr/spool/mail` &rarr; `/var/mail` – user mailboxes
- `/usr/tmp` &rarr; `/var/tmp` – preserved temporary files
- `/tmp` &rarr; `/tmp` – volatile temporary files
- `/etc` &rarr; `/etc` – configuration files
- `/usr/libexec` &rarr; `/usr/libexec` – helper daemons
- `/usr/local` &rarr; `/usr/local` – site-specific programs
- `/root` &rarr; `/root` – superuser home directory

Additional mappings may be required for subsystems like print spooling or
Kerberos databases, but the above examples cover common directories encountered
when modernizing historic BSD trees.

## Migration steps

1. Create the target directories following the FHS layout.
2. Move files from their historical paths while preserving ownership and
   permissions.
3. Provide compatibility symlinks from the old locations to the new ones during
   the transition period.
4. Update makefiles and scripts to use the new paths.
5. Document each mapping for future developers.

Following these steps alongside the broader plan in `reorg_plan.md` helps turn
the BSD distribution into a structure that is familiar to modern systems.
