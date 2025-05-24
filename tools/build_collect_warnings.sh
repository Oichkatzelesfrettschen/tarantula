#!/bin/sh
# Build userland with optional CSTD and ARCH flags and store warnings.
set -e
LOGDIR="build_logs"
mkdir -p "$LOGDIR"
ARCH_FLAGS=""
case "${ARCH}" in
    i686)
        ARCH_FLAGS="-m32"
        ;;
    x86_64)
        ARCH_FLAGS="-m64"
        ;;
esac

SRC_ULAND_DIR="${SRC_ULAND:-src-uland}"
make -C "$SRC_ULAND_DIR" CC="${CC:-cc}" CSTD="${CSTD:--std=c2x}" CFLAGS="${CFLAGS} ${ARCH_FLAGS}" \
    2>&1 | tee "$LOGDIR/build_${ARCH:-native}.log"
