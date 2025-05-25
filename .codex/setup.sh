#!/usr/bin/env bash
set -e

# ensure submodules are present
git submodule update --init --recursive >/dev/null 2>&1 || true

# Run repository setup for basic build tools
SCRIPT_DIR=$(cd "$(dirname "$0")/.." && pwd)
if [ -x "$SCRIPT_DIR/setup.sh" ]; then
  sudo "$SCRIPT_DIR/setup.sh" || true
fi

# Update package lists
sudo apt-get update -y >/dev/null 2>&1 || true

# Install build and analysis tools
APT_PKGS=(
  build-essential
  clang
  clang-tidy
  clang-tools
  lld
  lldb
  ccache
  ninja-build
  meson
  cmake
  bison
  flex
  byacc
  pkg-config
  libssl-dev
  agda
  agda-stdlib
  agda-mode
  coq
  coqide
  coq-theories
  tlaplus
  tla-bin
  isabelle
)
for pkg in "${APT_PKGS[@]}"; do
  sudo apt-get install -y "$pkg" >/dev/null 2>&1 || true
done

# Configure default optimization flags
cat <<'ENV' | sudo tee /etc/profile.d/tarantula.sh >/dev/null
export CC=clang
export CXX=clang++
export CFLAGS="-O3 -march=native"
export CXXFLAGS="-O3 -march=native"
export LDFLAGS="-fuse-ld=lld"
ENV

# Python helpers for analysis
PIP_PKGS=(compiledb buildcache configuredb pre-commit pytest)
for pkg in "${PIP_PKGS[@]}"; do
  pip3 install --break-system-packages "$pkg" >/dev/null 2>&1 || true
done

# configure pre-commit hooks when available
if command -v pre-commit >/dev/null 2>&1; then
  (cd "$SCRIPT_DIR" && pre-commit install --install-hooks >/dev/null 2>&1) || true
fi

pytest --version >/dev/null 2>&1 || true

# Useful npm tools
NPM_PKGS=(prettier eslint)
for pkg in "${NPM_PKGS[@]}"; do
  npm install -g "$pkg" >/dev/null 2>&1 || true
done

sudo apt-get clean >/dev/null 2>&1 || true

exit 0
