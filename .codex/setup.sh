#!/usr/bin/env bash
set -e

# Run repository setup for basic build tools
SCRIPT_DIR=$(cd "$(dirname "$0")/.." && pwd)
if [ -x "$SCRIPT_DIR/setup.sh" ]; then
  sudo "$SCRIPT_DIR/setup.sh" || true
fi

# Update package lists
sudo apt-get update -y >/dev/null 2>&1 || true

# Install theorem proving and verification tools
sudo apt-get install -y coq coqide coq-theories >/dev/null 2>&1 || true
# TLA+ tools are not packaged everywhere; attempt via apt or snap if available
sudo apt-get install -y tlaplus tla-bin >/dev/null 2>&1 || true

# Configure default optimization flags
cat <<'ENV' | sudo tee /etc/profile.d/tarantula.sh >/dev/null
export CC=clang
export CXX=clang++
export CFLAGS="-O3 -march=native"
export CXXFLAGS="-O3 -march=native"
export LDFLAGS="-fuse-ld=lld"
ENV

exit 0
