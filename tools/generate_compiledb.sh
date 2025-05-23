#!/usr/bin/env bash
set -euo pipefail
TARGET_DIR=${1:-usr/src}
compiledb -n bmake -C "$TARGET_DIR"
