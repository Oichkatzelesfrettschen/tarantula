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
