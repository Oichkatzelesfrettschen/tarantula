
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

The script now accepts a `--dry-run` flag for previewing changes. When run
without that flag it copies each legacy directory into `/usr`, removes the
original and replaces it with a symlink to the new path. After completion you
will find `bin`, `sbin`, `lib` and `libexec` symlinked to their counterparts in
`/usr`.

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

1. Run `tools/create_inventory.py` to snapshot the current tree. The generated
   `docs/file_inventory.txt` serves as a record of the pre-migration layout.
2. Prepare a chroot environment (or pass `--force`) and execute
   `tools/migrate_to_fhs.sh --dry-run` to review the planned actions.
3. Execute `tools/migrate_to_fhs.sh` without `--dry-run` to copy directories
   under `/usr` and replace the originals with symlinks.
4. Run `tools/organize_sources.sh` to relocate the source tree. This moves
   the kernel into `src-kernel`, user programs into `src-uland`, headers into
   `src-headers` and library objects into `src-lib`.
5. Verify the new symlinks by running `ls -l` on `bin`, `sbin` and related
   directories.
6. Update makefiles and scripts to reference the new paths. `grep -r "/bin"`
   can help locate hard-coded locations.
7. Once the build succeeds with the new layout, remove any compatibility links
   that are no longer needed.
8. Re-run `tools/create_inventory.py` so that `docs/file_inventory.txt` reflects
   the updated structure and commit the results alongside documentation notes.
9. Keep a log of each mapping for future developers.

Following these steps alongside the broader plan in `reorg_plan.md` helps turn
the BSD distribution into a structure that is familiar to modern systems.
## Remaining Manual Symlinks
Some directories are not handled by `migrate_to_fhs.sh` and must be linked manually.
After running `tools/organize_sources.sh` the kernel sources live in `src-kernel`.
Directories that still require manual handling include:
- `Domestic` - U.S. cryptography sources
- `Foreign` - externally maintained utilities
Record additional directories here as they are discovered.


