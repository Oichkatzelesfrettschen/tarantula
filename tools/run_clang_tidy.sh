#!/usr/bin/env bash
set -uo pipefail
LOG=/tmp/clang_tidy.log
rm -f "$LOG"
trap 'rc=$?; echo "FAILED: ${BASH_COMMAND} (exit $rc)" >> "$LOG"' ERR
file="$1"
args=("${@:2}")
if [[ "$file" == *.c ]]; then
    clang-tidy "$file" "${args[@]}" -- -std=c23
elif [[ "$file" == *.cpp || "$file" == *.cc || "$file" == *.cxx ]]; then
    clang-tidy "$file" "${args[@]}" -- -std=c++17
else
    clang-tidy "$file" "${args[@]}"
fi
