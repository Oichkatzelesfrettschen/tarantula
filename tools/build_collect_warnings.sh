#!/bin/sh
# Build userland with optional CSTD flag and store warnings.
set -e
LOGDIR="build_logs"
mkdir -p "$LOGDIR"
make -C usr/src CC="${CC:-cc}" CSTD="${CSTD:--std=c2x}" 2>&1 | tee "$LOGDIR/build.log"
