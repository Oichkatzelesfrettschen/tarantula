#!/usr/bin/env bash
set -euo pipefail
SRC_ULAND_DIR="${SRC_ULAND:-src-uland}"
TARGET_DIR=${1:-$SRC_ULAND_DIR}
compiledb -n bmake -C "$TARGET_DIR"
