#!/bin/sh
# Idempotent FHS migration helper
# Copies legacy top-level directories into /usr and rewrites symlinks.
# Refuses to run outside a chroot unless --force is given.
# A dry-run mode prints the actions without performing them.

set -e

usage() {
    echo "Usage: $0 [--force] [--dry-run]" >&2
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
DRYRUN=0
while [ $# -gt 0 ]; do
    case "$1" in
        --force)
            FORCE=1
            ;;
        --dry-run)
            DRYRUN=1
            ;;
        *)
            usage
            ;;
    esac
    shift
done

run_cmd() {
    if [ "$DRYRUN" -eq 1 ]; then
        echo "$*"
    else
        eval "$*"
    fi
}

move_and_link() {
    src="$1"
    dst="$2"

    [ -e "$src" ] || return 0

    run_cmd "mkdir -p $(dirname "$dst")"
    run_cmd "rsync -a \"$src/\" \"$dst/\""
    run_cmd "rm -rf \"$src\""
    run_cmd "ln -snf \"$dst\" \"$src\""
}

if ! in_chroot && [ "$FORCE" -ne 1 ]; then
    echo "Error: not running inside a chroot. Use --force to override." >&2
    exit 1
fi


# Ensure target directories exist
run_cmd mkdir -p usr/bin usr/sbin usr/lib usr/libexec

move_and_link bin usr/bin
move_and_link sbin usr/sbin
move_and_link lib usr/lib
move_and_link libexec usr/libexec

echo "FHS migration complete."
