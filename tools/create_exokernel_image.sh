#!/bin/sh
# Create a bootable disk image with the exokernel and user managers.
# Usage: create_exokernel_image.sh [image-path] [size]
# size defaults to 64M. Requires root privileges for mounting.

set -e

IMAGE=${1:-exokernel.img}
SIZE=${2:-64M}

KERNEL_BIN=${KERNEL_BIN:-src-kernel/exokernel}
INIT_BIN=${INIT_BIN:-src-uland/init/init}
FS_SERVER_BIN=${FS_SERVER_BIN:-src-uland/fs-server/fs_server}
PROC_MGR_BIN=${PROC_MGR_BIN:-src-uland/servers/proc_manager/proc_manager}

if [ ! -f "$KERNEL_BIN" ]; then
    echo "Missing kernel binary: $KERNEL_BIN" >&2
    exit 1
fi
for f in "$INIT_BIN" "$FS_SERVER_BIN" "$PROC_MGR_BIN"; do
    [ -f "$f" ] || { echo "Missing user program: $f" >&2; exit 1; }
done

# Create empty image and format it
dd if=/dev/zero of="$IMAGE" bs=1 count=0 seek=$SIZE
mke2fs -q "$IMAGE"

MNT=$(mktemp -d)
mount -o loop "$IMAGE" "$MNT"

mkdir -p "$MNT/boot" "$MNT/bin" "$MNT/sbin"
cp "$KERNEL_BIN" "$MNT/boot/"
cp "$INIT_BIN" "$MNT/sbin/init"
cp "$FS_SERVER_BIN" "$MNT/bin/"
cp "$PROC_MGR_BIN" "$MNT/bin/"

sync
umount "$MNT"
rmdir "$MNT"

echo "Created $IMAGE"
