#!/bin/sh
# Post-FHS cleanup helper
# Similar to organize_sources.sh but explicitly run after migrate_to_fhs.sh
# Moves kernel, userland and headers to consolidated locations.
# Usage: post_fhs_cleanup.sh [--force] [--dry-run]

set -e

usage() {
    echo "Usage: $0 [--force] [--dry-run]" >&2
    exit 1
}

# Determine if we're running inside a chroot
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
    if [ -L "$src" ] && [ "$(readlink "$src")" = "$dst" ]; then
        return 0
    fi
    run_cmd "mkdir -p \"$(dirname \"$dst\")\""
    run_cmd "rsync -a \"$src/\" \"$dst/\""
    run_cmd "rm -rf \"$src\""
    run_cmd "ln -snf \"$dst\" \"$src\""
}

move_artifacts() {
    base="$1"
    [ -d "$base" ] || return 0
    run_cmd "mkdir -p src-lib"
    find "$base" -type f \( -name '*.o' -o -name '*.a' -o -name '*.so' -o -name '*.so.*' \) | while read f; do
        rel="${f#$base/}"
        dest="src-lib/$rel"
        run_cmd "mkdir -p \"$(dirname \"$dest\")\""
        run_cmd "mv \"$f\" \"$dest\""
    done
}

if ! in_chroot && [ "$FORCE" -ne 1 ]; then
    echo "Error: not running inside a chroot. Use --force to override." >&2
    exit 1
fi

move_and_link sys src-kernel
move_and_link usr/src src-uland
move_and_link src-uland/include src-headers

move_artifacts src-uland
move_artifacts src-kernel

echo "Post-FHS source cleanup complete."
