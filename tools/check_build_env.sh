#!/usr/bin/env bash
# Simple helper to verify core build tools.
# Outputs missing tools and returns non-zero if any are absent.

missing=()
for cmd in cmake ninja meson clang bison flex clang-format clang-tidy; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    missing+=("$cmd")
  fi
done

# YACC must be explicitly set to "bison -y" after provisioning
if [ "${YACC:-}" != "bison -y" ]; then
  missing+=("YACC=\"bison -y\"")
fi

if [ ${#missing[@]} -eq 0 ]; then
  echo "All required build tools are present."
else
  echo "Missing build tools: ${missing[*]}" >&2
  exit 1
fi
