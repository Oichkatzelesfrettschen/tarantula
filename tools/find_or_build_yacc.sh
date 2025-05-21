#!/bin/sh
# Locate an available yacc implementation or build the bundled one via CMake.
set -e
if command -v yacc >/dev/null 2>&1; then
  command -v yacc
  exit 0
fi
if command -v bison >/dev/null 2>&1; then
  echo "$(command -v bison) -y"
  exit 0
fi
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
YACC_SRC="$ROOT_DIR/usr/src/usr.bin/yacc"
BUILD_DIR="$YACC_SRC/build"
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
if [ ! -f yacc ]; then
  cmake .. >/dev/null && make >/dev/null
fi
echo "$BUILD_DIR/yacc"
