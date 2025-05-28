#!/usr/bin/env bash
# Simple helper to verify core build tools.
# Outputs missing tools and returns non-zero if any are absent.

missing=()
# verify the minimal toolchain for the CMake/Ninja build
for cmd in cmake ninja clang bison flex clang-format clang-tidy; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    missing+=("$cmd")
  fi
done

# YACC should be set to "bison -y" after running setup.sh
if [ -z "${YACC:-}" ]; then
  missing+=("YACC env var")
fi

if [ ${#missing[@]} -eq 0 ]; then
  echo "All required build tools are present."
else
  echo "Missing build tools: ${missing[*]}" >&2
  exit 1
fi
