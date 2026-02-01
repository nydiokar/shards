# Slackware-Style Floppy Linux for Monster System

A minimal 1.44MB bootable floppy disk distribution running the 71-shard Monster framework.

## Specifications

- **Size**: 1.44MB (1,474,560 bytes)
- **Filesystem**: FAT12
- **Bootloader**: SYSLINUX
- **Kernel**: Linux (minimal config, no modules)
- **Userland**: BusyBox (static, minimal)
- **Init**: Custom shell script
- **Compression**: gzip -9

## Contents

```
/boot/vmlinuz       - Compressed Linux kernel
/boot/initrd.gz     - Compressed initramfs
/bin/busybox        - All Unix utilities
/bin/ingest         - Shard hash ingestion
/bin/distribute     - Shard distribution
/init               - Boot script
```

## Build

```bash
nix build .#floppy
```

## Run

```bash
# QEMU
nix run .#floppy

# Real hardware
dd if=result of=/dev/fd0 bs=1024

# VirtualBox
VBoxManage createvm --name "Monster71" --register
VBoxManage storagectl Monster71 --name "Floppy" --add floppy
VBoxManage storageattach Monster71 --storagectl "Floppy" --port 0 --device 0 --type fdd --medium result
```

## Boot Process

1. BIOS loads SYSLINUX from floppy
2. SYSLINUX loads kernel (vmlinuz)
3. Kernel unpacks initramfs (initrd.gz)
4. Init script runs:
   - Mount proc, sys, dev
   - Start shard 0 on port 7100
   - Drop to shell

## Size Optimization

- Kernel: No modules, minimal drivers
- BusyBox: Static binary, minimal applets
- Binaries: Stripped, release mode
- Compression: gzip -9 (best)
- Total: <1.44MB

## Network Boot (PXE)

```bash
# Extract kernel and initrd
mcopy -i result ::vmlinuz .
mcopy -i result ::initrd.gz .

# TFTP server
cp vmlinuz /tftpboot/
cp initrd.gz /tftpboot/

# PXE config
cat > /tftpboot/pxelinux.cfg/default <<EOF
DEFAULT monster
LABEL monster
  KERNEL vmlinuz
  APPEND initrd=initrd.gz
EOF
```

## Multi-Floppy Set

For complete 71-shard system:

- Disk 1: Boot + Shard 0-9
- Disk 2: Shard 10-19
- ...
- Disk 8: Shard 70 + docs

```bash
nix build .#floppy-set
```
