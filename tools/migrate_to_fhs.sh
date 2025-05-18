#!/bin/sh
# Idempotent FHS migration helper
# Copies legacy top-level directories into /usr and rewrites symlinks.
# Refuses to run outside a chroot unless --force is given.

set -e

usage() {
    echo "Usage: $0 [--force]" >&2
    exit 1
}

# Detect if we are running inside a chroot by comparing / and /proc/1/root
in_chroot() {
    if [ "$(stat -c %d:%i / 2>/dev/null)" != "$(stat -c %d:%i /proc/1/root 2>/dev/null)" ]; then
        return 0
    fi
    return 1
}

FORCE=0
if [ "$1" = "--force" ]; then
    FORCE=1
elif [ -n "$1" ]; then
    usage
fi

if ! in_chroot && [ "$FORCE" -ne 1 ]; then
    echo "Error: not running inside a chroot. Use --force to override." >&2
    exit 1
fi

# Ensure target directories exist
mkdir -p usr/bin usr/sbin usr/lib usr/libexec

rsync -a bin/ usr/bin/
rsync -a sbin/ usr/sbin/
rsync -a lib/ usr/lib/
rsync -a libexec/ usr/libexec/

ln -snf usr/bin bin
ln -snf usr/sbin sbin
ln -snf usr/lib lib
ln -snf usr/libexec libexec

echo "FHS migration complete."
