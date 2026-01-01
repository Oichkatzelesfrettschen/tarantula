#!/bin/bash
# Build userland with optional CSTD and ARCH flags and store warnings.
#
# Enable strict mode:
#   -e  : exit immediately on errors
#   -u  : treat unset variables as an error
#   -o pipefail : capture failures across piped commands
set -euo pipefail
LOGDIR="build_logs"
mkdir -p "$LOGDIR"
ARCH_FLAGS=""
# Evaluate optional ARCH flag; default to native when unset.
case "${ARCH:-}" in
    i686)
        ARCH_FLAGS="-m32"
        ;;
    x86_64)
        ARCH_FLAGS="-m64"
        ;;
esac

SRC_ULAND_DIR="${SRC_ULAND:-src-uland}"
if [ ! -f "$SRC_ULAND_DIR/Makefile" ]; then
    echo "Expected Makefile in '$SRC_ULAND_DIR' not found. Generate build files or set SRC_ULAND." >&2
    exit 1
fi
make -C "$SRC_ULAND_DIR" \
    CC="${CC:-cc}" \
    CSTD="${CSTD:--std=c2x}" \
    CFLAGS="${CFLAGS:-} ${ARCH_FLAGS}" \
    2>&1 | tee "$LOGDIR/build_${ARCH:-native}.log"
