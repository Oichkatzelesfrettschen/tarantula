#!/usr/bin/env bash
set -euo pipefail
SRC_ULAND_DIR="${SRC_ULAND:-src-uland}"
TARGET_DIR=${1:-$SRC_ULAND_DIR}
cmake -S "$TARGET_DIR" -B "$TARGET_DIR/build" -G Ninja \
      -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
ninja -C "$TARGET_DIR/build"
cp "$TARGET_DIR/build/compile_commands.json" "$TARGET_DIR/compile_commands.json"
