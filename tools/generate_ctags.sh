#!/bin/sh
# Generate tags for the source tree
SRC_ULAND_DIR="${SRC_ULAND:-src-uland}"
SRC_KERNEL_DIR="${SRC_KERNEL:-src-kernel}"
ctags -R "$SRC_ULAND_DIR" "$SRC_KERNEL_DIR"
