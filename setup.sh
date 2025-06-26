#!/usr/bin/env bash
#───────────────────────────────────────────────────────────────────────────────
#  setup.sh — Bootstrap tool-chains for the Research-UNIX resurrection project
#
#  Features
#  ────────────────────────────────────────────────────────────────────────────
#  • Online / offline installation with per-package retry & local caches
#  • Three independent install buckets:
#       --core   → compilers, build tools, analysis utilities
#       --langs  → high-level language runtimes (Go, Rust, Lua, …)
#       --cross  → cross compilers & QEMU targets
#    ( --all is the default when none are specified )
#  • Graceful failure logging (does NOT abort on first error)
#  • Curl head checks for all remote assets, URL strike-through in README.md
#  • Pinned protoc 25.1, IA-16 cross-compiler, and bison → yacc export
#  • Single ISO-time-stamped log file at /tmp/setup.log
#  • Idempotent — re-runs reuse cached .deb / wheel / tgz artifacts
#───────────────────────────────────────────────────────────────────────────────
set -euo pipefail
IFS=$'\n\t'

################################################################################
#  0. Global variables & logging helpers
################################################################################

LOG_FILE=/tmp/setup.log
: > "$LOG_FILE"                        # truncate on every run

log() { printf '%(%F %T%z)T  %s\n' -1 "$*" | tee -a "$LOG_FILE" ; }

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
CACHE_DIR="$SCRIPT_DIR/third_party"
APT_CACHE="$CACHE_DIR/apt"
PIP_CACHE="$CACHE_DIR/pip"
OFFLINE_PKG_DIR="$CACHE_DIR/offline"
README_URL_FAIL="$SCRIPT_DIR/README.md"

mkdir -p "$APT_CACHE" "$PIP_CACHE" "$OFFLINE_PKG_DIR"

################################################################################
#  1. CLI flags & defaults
################################################################################

OFFLINE_MODE=0
DO_CORE=0
DO_LANGS=0
DO_CROSS=0

usage() {
  cat <<EOF
Usage: $0 [--offline] [--core] [--langs] [--cross] [--all]

  --offline   Assume no network, install only from cached artefacts
  --core      Install core build / analysis tool-chain
  --langs     Install language runtimes (Go, Rust, Python, …)
  --cross     Install cross compilers, qemu, IA-16 tool-chain
  --all       Install everything (default if no bucket is requested)
  --help      Show this help
EOF
  exit 0
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --offline) OFFLINE_MODE=1 ;;
    --core)    DO_CORE=1      ;;
    --langs|--languages) DO_LANGS=1 ;;
    --cross)   DO_CROSS=1     ;;
    --all)     DO_CORE=1; DO_LANGS=1; DO_CROSS=1 ;;
    --help|-h) usage ;;
    *) log "Unknown flag: $1"; usage ;;
  esac
  shift
done

# Default bucket selection when none provided
if (( DO_CORE + DO_LANGS + DO_CROSS == 0 )); then
  DO_CORE=1; DO_LANGS=1; DO_CROSS=1
fi

################################################################################
#  2. Failure accumulators
################################################################################

APT_FAILED=()
PIP_FAILED=()
NPM_FAILED=()

trap 'log "FAILED cmd: ${BASH_COMMAND} (exit $?)"' ERR
export DEBIAN_FRONTEND=noninteractive

################################################################################
#  3. Helper functions
################################################################################

curl_head() { curl --head -fsSL "$1" >/dev/null 2>&1; }

record_url_fail() { echo "~~$1~~" >> "$README_URL_FAIL"; }

curl_check() {
  if ! curl_head "$1"; then
    log "URL UNREACHABLE $1"
    record_url_fail "$1"
    return 1
  fi
}

apt_attempt() {
  local pkg="$1"
  # 3.1  offline .deb cache
  if (( OFFLINE_MODE )); then
    local deb
    deb=$(ls "$OFFLINE_PKG_DIR"/${pkg}_*.deb 2>/dev/null | sort -V | tail -n1 || true)
    if [[ -n $deb ]]; then
      dpkg -i "$deb" >/dev/null 2>&1 && { log "OFFLINE OK  $pkg"; return 0; }
      log "OFFLINE FAIL $pkg"
    else
      log "OFFLINE MISS $pkg"
    fi
    APT_FAILED+=("$pkg"); return 1
  fi

  # 3.2  cached .deb from previous run
  local deb
  deb=$(ls "$APT_CACHE"/${pkg}_*.deb 2>/dev/null | sort -V | tail -n1 || true)
  if [[ -n $deb ]]; then
    dpkg -i "$deb" >/dev/null 2>&1 && { log "APT OK  $pkg (cached)"; return 0; }
  fi

  # 3.3  normal apt install (exact version when available)
  local ver
  ver=$(apt-cache show "$pkg" 2>/dev/null | awk '/^Version:/{print $2; exit}' || true)
  if apt-get install -y "${ver:+${pkg}=${ver}}" "${ver:+" "}" >/dev/null 2>&1; then
    log "APT OK  $pkg"
    apt-get -y download "$pkg"  >/dev/null 2>&1 && mv ${pkg}_*.deb "$APT_CACHE"/ 2>/dev/null || true
    return 0
  fi

  log "APT FAIL $pkg"
  APT_FAILED+=("$pkg"); return 1
}

pip_attempt() {
  local pkg="$1"
  local wheel tarball
  wheel=$(ls "$PIP_CACHE"/${pkg}-*.whl 2>/dev/null | sort -V | tail -n1 || true)
  tarball=$(ls "$PIP_CACHE"/${pkg}-*.tar.gz 2>/dev/null | sort -V | tail -n1 || true)

  for src in "$wheel" "$tarball"; do
    [[ -z $src ]] && continue
    if pip3 install "$src" >/dev/null 2>&1; then
      log "PIP OK  $pkg (cached)"
      return 0
    fi
  done

  if pip3 install "$pkg" >/dev/null 2>&1; then
    log "PIP OK  $pkg"
    pip3 download "$pkg" -d "$PIP_CACHE" >/dev/null 2>&1 || true
    return 0
  fi

  log "PIP FAIL $pkg"
  PIP_FAILED+=("$pkg"); return 1
}

npm_attempt() {
  local pkg="$1"
  if npm -g install "$pkg" >/dev/null 2>&1; then
    log "NPM OK  $pkg"
    return 0
  fi
  log "NPM FAIL $pkg"
  NPM_FAILED+=("$pkg"); return 1
}

retry_failures() {
  log "Retrying failed packages (if any)"
  local pkg leftovers=()
  for pkg in "${APT_FAILED[@]}";  do apt_attempt "$pkg" || leftovers+=("$pkg"); done
  APT_FAILED=("${leftovers[@]}"); leftovers=()
  for pkg in "${PIP_FAILED[@]}";  do pip_attempt "$pkg" || leftovers+=("$pkg"); done
  PIP_FAILED=("${leftovers[@]}"); leftovers=()
  for pkg in "${NPM_FAILED[@]}";  do npm_attempt "$pkg" || leftovers+=("$pkg"); done
  NPM_FAILED=("${leftovers[@]}")
}

################################################################################
#  4. Phased installation buckets
################################################################################

install_core() {
  log "=== Installing CORE tool-chain ==="
  local pkgs=(
    build-essential gcc g++ clang lld llvm ninja-build make
    cmake meson autoconf automake libtool m4 gawk flex bison byacc
    clang-format clang-tidy uncrustify astyle editorconfig pre-commit
    shellcheck codespell pkg-config file ca-certificates curl git unzip
    strace ltrace linux-perf systemtap systemtap-sdt-dev crash valgrind
    kcachegrind trace-cmd kernelshark llvm-polly llvm-bolt
    graphviz doxygen python3-sphinx cloc cscope cflow plantuml
    libasan6 libubsan1 likwid hwloc libopenblas-dev liblapack-dev libeigen3-dev
  )
  for pkg in "${pkgs[@]}"; do apt_attempt "$pkg" || pip_attempt "$pkg" || npm_attempt "$pkg"; done

  #  bison → yacc export
  if command -v bison >/dev/null 2>&1; then
    export YACC="bison -y"
    echo 'export YACC="bison -y"' > /etc/profile.d/yacc.sh
    ln -sf "$(command -v bison)" /usr/local/bin/yacc
  else
    log "ERROR: bison missing after install"
  fi

  #  pre-commit hook
  if command -v pre-commit >/dev/null 2>&1; then
    (cd "$SCRIPT_DIR" && pre-commit install --install-hooks) || true
  fi
}

install_langs() {
  log "=== Installing LANGUAGE runtimes ==="
  local pkgs=(
    golang-go nodejs npm typescript rustc cargo clippy rustfmt
    lua5.4 liblua5.4-dev luarocks
    ghc cabal-install hlint stylish-haskell
    sbcl ecl clisp slime
    ldc gdc dmd-compiler dub
    openjdk-17-jdk maven gradle dotnet-sdk-8 mono-complete
    swift kotlin ruby ruby-dev bundler
    php-cli composer r-base dart gnat gfortran
    zig nim crystal gforth
  )
  for pkg in "${pkgs[@]}"; do apt_attempt "$pkg" || pip_attempt "$pkg" || npm_attempt "$pkg"; done

  #  Python scientific stack + ML
  local py_pkgs=(
    python3 python3-pip python3-dev python3-venv python3-wheel
    python3-numpy python3-scipy python3-pandas python3-matplotlib
    python3-scikit-learn python3-torch python3-torchvision python3-onnxruntime
  )
  for pkg in "${py_pkgs[@]}"; do apt_attempt "$pkg" || pip_attempt "$pkg"; done

  #  pip-only tools
  local pip_tools=( lizard gprof2dot black ruff pytest pylint )
  for p in "${pip_tools[@]}"; do pip_attempt "$p"; done
}

install_cross() {
  log "=== Installing CROSS compilers & QEMU ==="
  # QEMU (all targets)
  local qemu_pkgs=(
    qemu-user-static qemu-utils
    qemu-system-x86 qemu-system-arm qemu-system-aarch64
    qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64
  )
  for pkg in "${qemu_pkgs[@]}"; do apt_attempt "$pkg"; done

  # Debian cross-compiler packages (main architectures)
  local arches=(
    ia64 i686 aarch64 armel armhf arm64 riscv64 powerpc powerpc64 powerpc64le
    m68k hppa loongarch64 mips mipsel mips64 mips64el
  )
  for arch in "${arches[@]}"; do
    apt_attempt gcc-"$arch"-linux-gnu || true
    apt_attempt g++-"$arch"-linux-gnu || true
  done

  #  IA-16 (8086/286) cross tool-chain
  local ia16_url ia16_ver
  ia16_url=$(curl -fsSL https://api.github.com/repos/tkchia/gcc-ia16/releases/latest |
             awk -F\" '/browser_download_url/ && /linux64.tar.xz/{print $4; exit}' || true)
  if [[ -n $ia16_url ]]; then
    curl_check "$ia16_url" &&
    curl -fsSL "$ia16_url" -o /tmp/ia16.tar.xz &&
    tar -xf /tmp/ia16.tar.xz -C /opt &&
    echo 'export PATH=/opt/ia16-elf-gcc/bin:$PATH' > /etc/profile.d/ia16.sh &&
    export PATH=/opt/ia16-elf-gcc/bin:$PATH &&
    log "IA-16 tool-chain installed"
  else
    log "FAIL to resolve IA-16 release URL"
    APT_FAILED+=("ia16-elf-gcc")
  fi
}

install_protoc() {
  log "-- Installing pinned protoc 25.1 --"
  local ver=25.1
  local url="https://github.com/protocolbuffers/protobuf/releases/download/v${ver}/protoc-${ver}-linux-x86_64.zip"
  local zip=/tmp/protoc.zip
  curl_check "$url" && curl -fsSL "$url" -o "$zip" &&
  unzip -q "$zip" -d /usr/local && rm -f "$zip" &&
  log "protoc ${ver} installed" || APT_FAILED+=("protoc")
}

################################################################################
#  5. Pre-flight APT update / offline detection
################################################################################

if (( ! OFFLINE_MODE )); then
  if ! apt-get -qq update; then
    OFFLINE_MODE=1
    log "Network unreachable → switching to OFFLINE mode"
  else
    log "APT OK  initial update"
  fi
fi

################################################################################
#  6. Bucket execution
################################################################################

(( DO_CORE  )) && install_core
(( DO_LANGS )) && install_langs
(( DO_CROSS )) && install_cross
install_protoc

################################################################################
#  7. Finalisation, cleanup & retry
################################################################################

apt-get clean -qq
rm -rf /var/lib/apt/lists/*

retry_failures

if (( ${#APT_FAILED[@]} + ${#PIP_FAILED[@]} + ${#NPM_FAILED[@]} > 0 )); then
  log "===   FINAL REPORT: some packages could not be installed   ==="
  [[ ${#APT_FAILED[@]} -gt 0 ]] && log "APT:  ${APT_FAILED[*]}"
  [[ ${#PIP_FAILED[@]} -gt 0 ]] && log "PIP:  ${PIP_FAILED[*]}"
  [[ ${#NPM_FAILED[@]} -gt 0 ]] && log "NPM:  ${NPM_FAILED[*]}"
  exit 1
fi

log "Setup completed successfully"
exit 0
