#!/bin/sh
# Generate cscope.files for the source tree
find usr/src sys -name '*.[chsyl]' > cscope.files
cscope -b -q -k
