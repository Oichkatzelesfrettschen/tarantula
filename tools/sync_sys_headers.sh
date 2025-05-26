#!/bin/sh
# Synchronize kernel headers into src-headers/sys
# Usage: sync_sys_headers.sh [--dry-run]
# Copies headers from usr/src/sys/sys to src-headers/sys and replaces the
# original directory with a symlink. Intended to unify the header tree.

set -e

usage() {
    echo "Usage: $0 [--dry-run]" >&2
    exit 1
}

DRYRUN=0
while [ $# -gt 0 ]; do
    case "$1" in
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

SRC_DIR="usr/src/sys/sys"
DST_DIR="src-headers/sys"

run_cmd "mkdir -p \"$DST_DIR\""
run_cmd "rsync -a \"$SRC_DIR/\" \"$DST_DIR/\""

if [ ! -L "$SRC_DIR" ]; then
    run_cmd "rm -rf \"$SRC_DIR\""
    run_cmd "ln -snf ../../../$DST_DIR \"$SRC_DIR\""
fi

echo "Kernel headers synchronized to $DST_DIR."
