#!/usr/bin/env bash
set -uo pipefail
LOG=/tmp/clang_tidy.log
rm -f "$LOG"
trap 'rc=$?; echo "FAILED: ${BASH_COMMAND} (exit $rc)" >> "$LOG"' ERR
file="$1"
shift
# Drop a leading '--' added by makefiles
if [[ "$1" == "--" ]]; then
    shift
fi
args=("$@")
if [[ "$file" == *.c ]]; then
    # Match the C standard used by the makefiles (-std=c2x)
    clang-tidy "$file" -- "${args[@]}" -std=c2x
elif [[ "$file" == *.cpp || "$file" == *.cc || "$file" == *.cxx ]]; then
    clang-tidy "$file" -- "${args[@]}" -std=c++17
else
    clang-tidy "$file" -- "${args[@]}"
fi
