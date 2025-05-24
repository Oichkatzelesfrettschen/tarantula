#!/bin/sh
# Generate cscope.files for the source tree
SRC_ULAND_DIR="${SRC_ULAND:-src-uland}"
SRC_KERNEL_DIR="${SRC_KERNEL:-src-kernel}"
find "$SRC_ULAND_DIR" "$SRC_KERNEL_DIR" -name '*.[chsyl]' > cscope.files
cscope -b -q -k
