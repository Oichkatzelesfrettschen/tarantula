#!/usr/bin/env bash
set -u -o pipefail

# log all successes and failures
LOG_FILE=/tmp/setup.log
rm -f "$LOG_FILE"

# record failing commands without stopping execution
trap 'rc=$?; echo "FAILED cmd: ${BASH_COMMAND} (exit $rc)" >> "$LOG_FILE"' ERR
export DEBIAN_FRONTEND=noninteractive

# collect failures rather than exiting on the first error
APT_FAILED=()
PIP_FAILED=()

# helper to pin to the repo’s exact version if it exists
apt_pin_install(){
  pkg="$1"
  ver=$(apt-cache show "$pkg" 2>/dev/null \
        | awk '/^Version:/{print $2; exit}')
  if [ -n "$ver" ]; then
    apt-get install -y "${pkg}=${ver}" >/dev/null 2>&1
  else
    apt-get install -y "$pkg" >/dev/null 2>&1
  fi
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "APT FAIL $pkg" >> "$LOG_FILE"
    APT_FAILED+=("$pkg")
    return 1
  else
    echo "APT OK   $pkg" >> "$LOG_FILE"
    return 0
  fi
}

# fallback installer using pip3 when apt fails
install_with_pip(){
  pkg="$1"
  pip3 install "$pkg" >/dev/null 2>&1
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "PIP FAIL $pkg" >> "$LOG_FILE"
    PIP_FAILED+=("$pkg")
    return 1
  else
    echo "PIP OK   $pkg" >> "$LOG_FILE"
    return 0
  fi
}

# attempt to build bmake from upstream source if package install fails
build_bmake_from_source(){
  url="https://ftp.NetBSD.org/pub/NetBSD/misc/sjg/bmake.tar.gz"
  tmpdir=$(mktemp -d)
  if curl -fsSL "$url" -o "$tmpdir/bmake.tar.gz"; then
    tar -xzf "$tmpdir/bmake.tar.gz" -C "$tmpdir"
    srcdir=$(find "$tmpdir" -maxdepth 1 -type d -name "bmake*")
    (cd "$srcdir" && ./boot-strap --prefix=/usr/local >/dev/null 2>&1)
    rc=$?
    if [ $rc -ne 0 ]; then
      echo "SRC FAIL bmake" >> "$LOG_FILE"
      APT_FAILED+=("bmake-source")
    else
      echo "SRC OK   bmake" >> "$LOG_FILE"
      # create a minimal deb so dpkg records bmake as installed
      pkgdir=$(mktemp -d)
      mkdir -p "$pkgdir/DEBIAN"
      cat > "$pkgdir/DEBIAN/control" <<EOF
Package: bmake
Version: 2024-source
Section: misc
Priority: optional
Architecture: $(dpkg --print-architecture)
Maintainer: local
Description: locally built bmake
EOF
      dpkg-deb --build "$pkgdir" >/dev/null 2>&1
      dpkg -i "$pkgdir.deb" >/dev/null 2>&1
      rm -rf "$pkgdir" "$pkgdir.deb"
    fi
  else
    echo "SRC DL   FAIL bmake" >> "$LOG_FILE"
    APT_FAILED+=("bmake-source-download")
  fi
}

# enable foreign architectures for cross-compilation
for arch in i386 armel armhf arm64 riscv64 powerpc ppc64el ia64; do
  dpkg --add-architecture "$arch"
done
# update package lists
apt-get update -y >/dev/null 2>&1 && echo "APT OK   update" >> "$LOG_FILE" || {
  echo "APT FAIL update" >> "$LOG_FILE"
  APT_FAILED+=("update")
}
# guarantee bmake (with its mk framework) is present
# mk-configure is optional and layers an Autotools-style system on top
apt_pin_install bmake || install_with_pip bmake
command -v bmake >/dev/null 2>&1 || build_bmake_from_source
apt_pin_install mk-configure || install_with_pip mk-configure
apt_pin_install bison || install_with_pip bison
apt_pin_install byacc || install_with_pip byacc
apt_pin_install shellcheck || install_with_pip shellcheck

# core build tools, formatters, analysis, science libs
for pkg in \
  build-essential gcc g++ clang lld llvm \
  clang-format clang-tidy uncrustify astyle editorconfig pre-commit shellcheck \
  make bmake ninja-build cmake meson \
  autoconf automake libtool m4 gawk flex bison byacc \
  pkg-config file ca-certificates curl git unzip \
  libopenblas-dev liblapack-dev libeigen3-dev \
  libbsd0 libbsd-dev \
  strace ltrace linux-perf systemtap systemtap-sdt-dev crash \
  valgrind kcachegrind trace-cmd kernelshark \
  libasan6 libubsan1 likwid hwloc; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done

# Python & deep-learning / MLOps
for pkg in \
  python3 python3-pip python3-dev python3-venv python3-wheel \
  python3-numpy python3-scipy python3-pandas \
  python3-matplotlib python3-scikit-learn \
  python3-torch python3-torchvision python3-torchaudio \
  python3-onnx python3-onnxruntime; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done


for pip_pkg in \
  tensorflow-cpu jax jaxlib \
  tensorflow-model-optimization mlflow onnxruntime-tools \
  meson ninja cmake pre-commit compiledb; do
  pip3 install "$pip_pkg" >/dev/null 2>&1
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "PIP FAIL $pip_pkg" >> "$LOG_FILE"
    PIP_FAILED+=("$pip_pkg")
  else
    echo "PIP OK   $pip_pkg" >> "$LOG_FILE"
  fi
done

# set up pre-commit hooks if available
if command -v pre-commit >/dev/null 2>&1; then
  (cd "$(dirname "$0")" && pre-commit install --install-hooks) || {
    echo "PIP FAIL pre-commit hook" >> "$LOG_FILE"
    PIP_FAILED+=("pre-commit")
  }
else
  echo "PIP FAIL pre-commit" >> "$LOG_FILE"
  PIP_FAILED+=("pre-commit")
fi

# QEMU emulation for foreign binaries
for pkg in \
  qemu-user-static \
  qemu-system-x86 qemu-system-arm qemu-system-aarch64 \
  qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64 qemu-utils; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done

# multi-arch cross-compilers
for pkg in \
  bcc bin86 elks-libc \
  gcc-ia64-linux-gnu g++-ia64-linux-gnu \
  gcc-i686-linux-gnu g++-i686-linux-gnu \
  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  gcc-arm-linux-gnueabi g++-arm-linux-gnueabi \
  gcc-arm-linux-gnueabihf g++-arm-linux-gnueabihf \
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu \
  gcc-powerpc-linux-gnu g++-powerpc-linux-gnu \
  gcc-powerpc64-linux-gnu g++-powerpc64-linux-gnu \
  gcc-powerpc64le-linux-gnu g++-powerpc64le-linux-gnu \
  gcc-m68k-linux-gnu g++-m68k-linux-gnu \
  gcc-hppa-linux-gnu g++-hppa-linux-gnu \
  gcc-loongarch64-linux-gnu g++-loongarch64-linux-gnu \
  gcc-mips-linux-gnu g++-mips-linux-gnu \
  gcc-mipsel-linux-gnu g++-mipsel-linux-gnu \
  gcc-mips64-linux-gnuabi64 g++-mips64-linux-gnuabi64 \
  gcc-mips64el-linux-gnuabi64 g++-mips64el-linux-gnuabi64; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done

# high-level language runtimes and tools
for pkg in \
  golang-go nodejs npm typescript \
  rustc cargo clippy rustfmt \
  lua5.4 liblua5.4-dev luarocks \
  ghc cabal-install hlint stylish-haskell \
  sbcl ecl clisp cl-quicklisp slime cl-asdf \
  ldc gdc dmd-compiler dub libphobos-dev \
  chicken-bin libchicken-dev chicken-doc \
  openjdk-17-jdk maven gradle dotnet-sdk-8 mono-complete \
  swift swift-lldb swiftpm kotlin gradle-plugin-kotlin \
  ruby ruby-dev gem bundler php-cli php-dev composer phpunit \
  r-base r-base-dev dart flutter gnat gprbuild gfortran gnucobol \
  fpc lazarus zig nim nimble crystal shards gforth; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done

if ! command -v swift >/dev/null 2>&1; then
  echo "Swift not found after installation" >&2
fi

# GUI & desktop-dev frameworks
for pkg in \
  libqt5-dev qtcreator libqt6-dev \
  libgtk1.2-dev libgtk2.0-dev libgtk-3-dev libgtk-4-dev \
  libfltk1.3-dev xorg-dev libx11-dev libxext-dev \
  libmotif-dev openmotif cde \
  xfce4-dev-tools libxfce4ui-2-dev lxde-core lxqt-dev-tools \
  libefl-dev libeina-dev \
  libwxgtk3.0-dev libwxgtk3.0-gtk3-dev \
  libsdl2-dev libsdl2-image-dev libsdl2-ttf-dev \
  libglfw3-dev libglew-dev; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done

# containers, virtualization, HPC, debug
for pkg in \
  docker.io podman buildah virt-manager libvirt-daemon-system qemu-kvm \
  gdb lldb perf gcovr lcov bcc-tools bpftrace \
  openmpi-bin libopenmpi-dev mpich; do
  apt_pin_install "$pkg" || install_with_pip "$pkg"
done

# IA-16 (8086/286) cross-compiler
IA16_JSON=$(curl -fsSL https://api.github.com/repos/tkchia/gcc-ia16/releases/latest)
rc=$?
if [ $rc -ne 0 ] || [ -z "$IA16_JSON" ]; then
  echo "curl FAILED ia16 version" >> "$LOG_FILE"
  APT_FAILED+=("ia16-elf-gcc")
else
  IA16_VER=$(echo "$IA16_JSON" | awk -F\" '/tag_name/{print $4; exit}')
  if [ -z "$IA16_VER" ]; then
    echo "curl FAILED ia16 version parse" >> "$LOG_FILE"
    APT_FAILED+=("ia16-elf-gcc")
  else
    if curl -fsSL "https://github.com/tkchia/gcc-ia16/releases/download/${IA16_VER}/ia16-elf-gcc-linux64.tar.xz" -o /tmp/ia16.tar.xz; then
      tar -Jx -f /tmp/ia16.tar.xz -C /opt
      echo 'export PATH=/opt/ia16-elf-gcc/bin:$PATH' > /etc/profile.d/ia16.sh
      export PATH=/opt/ia16-elf-gcc/bin:$PATH
    else
      echo "curl FAILED ia16-elf-gcc" >> "$LOG_FILE"
      APT_FAILED+=("ia16-elf-gcc")
    fi
  fi
fi

# protoc installer (pinned)
PROTO_VERSION=25.1
if curl -fsSL "https://raw.githubusercontent.com/protocolbuffers/protobuf/v${PROTO_VERSION}/protoc-${PROTO_VERSION}-linux-x86_64.zip" -o /tmp/protoc.zip; then
  unzip -d /usr/local /tmp/protoc.zip
  rm /tmp/protoc.zip
else
  echo "curl FAILED protoc" >> "$LOG_FILE"
  APT_FAILED+=("protoc")
fi


# ensure yacc points to bison and gmake invokes bmake
if command -v bison >/dev/null 2>&1; then
  ln -sf "$(command -v bison)" /usr/local/bin/yacc
fi

command -v gmake >/dev/null 2>&1 || {
  if command -v bmake >/dev/null 2>&1; then
    ln -s "$(command -v bmake)" /usr/local/bin/gmake
  else
    ln -s "$(command -v make)" /usr/local/bin/gmake
  fi
}

# verify bmake was installed successfully
if ! command -v bmake >/dev/null 2>&1; then
  echo "bmake not found after installation" >&2
  exit 1
fi

# ensure the package itself is registered with dpkg
if ! dpkg -s bmake >/dev/null 2>&1; then
  echo "bmake package is not installed" >&2
  exit 1
fi

# clean up
apt-get clean
rm -rf /var/lib/apt/lists/*

if [ ${#APT_FAILED[@]} -ne 0 ] || [ ${#PIP_FAILED[@]} -ne 0 ]; then
  echo "Some downloads or installations failed. See $LOG_FILE for details." >&2
  [ ${#APT_FAILED[@]} -ne 0 ] && echo "APT/download failures: ${APT_FAILED[*]}" >&2
  [ ${#PIP_FAILED[@]} -ne 0 ] && echo "PIP failures: ${PIP_FAILED[*]}" >&2
fi

exit 0
