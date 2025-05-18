
# Migrating to an FHS Layout

This repository preserves the historic 4.4BSD tree which places `bin`, `sbin` and
other directories at the root of the filesystem. The `tools/migrate_to_fhs.sh`
script converts the layout to a more modern FHS style by copying these
directories under `/usr` and creating the appropriate symlinks.

The script is idempotent and may be rerun to update files as needed. By default
it only executes when run inside a chroot to avoid modifying a live system.
Pass `--force` to override this safety check.

```sh
# Inside the chroot
/tools/migrate_to_fhs.sh

# Or outside
sudo tools/migrate_to_fhs.sh --force
```

After running the script you will find `bin`, `sbin`, `lib` and `libexec`
symlinked to their counterparts in `/usr`.

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

