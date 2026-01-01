#!/usr/bin/env bash
# -----------------------------------------------------------------------------
# setup.sh - Provision offline package directories for BSD/Tarantula.
#
# This script configures paths for caching dependencies when network access is
# restricted.  It establishes an OFFLINE_PKG_DIR environment variable pointing
# to the repository's `offline_packages/` directory and ensures that all
# required directories exist for later use by packaging tools or manual
# installation steps.
# -----------------------------------------------------------------------------
set -euo pipefail

# Resolve the absolute path to the repository root, i.e. the directory that
# contains this script. This allows the script to be invoked from any working
# directory while still locating the offline cache correctly.
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Directory for offline package archives.  Exported so subshells and invoked
# tools can rely on this location.
export OFFLINE_PKG_DIR="${REPO_ROOT}/offline_packages"

# Ensure the required directory hierarchy exists.  The script maintains a flat
# structure for Debian packages under OFFLINE_PKG_DIR and prepares auxiliary
# caches for `apt` and `pip` under `third_party`.
mkdir -p "${OFFLINE_PKG_DIR}" \
         "${REPO_ROOT}/third_party/apt" \
         "${REPO_ROOT}/third_party/pip"

# Provide feedback so callers know where the offline cache resides.
printf 'Offline packages will be loaded from: %s\n' "${OFFLINE_PKG_DIR}"
