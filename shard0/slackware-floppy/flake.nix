{
  description = "Slackware-style floppy disk Linux for 71-shard Monster system";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      
      # Minimal kernel for floppy
      kernel = pkgs.linux.override {
        structuredExtraConfig = with pkgs.lib.kernel; {
          EMBEDDED = yes;
          EXPERT = yes;
          MODULES = no;
          BLK_DEV_INITRD = yes;
          CRAMFS = yes;
          SQUASHFS = yes;
        };
      };
      
      # Minimal busybox userland
      busybox = pkgs.busybox.override {
        enableStatic = true;
        enableMinimal = true;
      };
      
      # Build shard binaries
      shardBinaries = pkgs.stdenv.mkDerivation {
        name = "shard-binaries";
        src = ../hash;
        buildInputs = [ pkgs.rustc pkgs.cargo ];
        buildPhase = ''
          cargo build --release --bin ingest
          cargo build --release --bin distribute
        '';
        installPhase = ''
          mkdir -p $out/bin
          cp target/release/ingest $out/bin/
          cp target/release/distribute $out/bin/
          strip $out/bin/*
        '';
      };
      
      # Create initramfs
      initramfs = pkgs.makeInitrd {
        contents = [
          { object = "${busybox}/bin/busybox"; symlink = "/bin/busybox"; }
          { object = "${shardBinaries}/bin/ingest"; symlink = "/bin/ingest"; }
          { object = "${shardBinaries}/bin/distribute"; symlink = "/bin/distribute"; }
          { object = pkgs.writeScript "init" ''
              #!/bin/busybox sh
              /bin/busybox --install -s
              mount -t proc proc /proc
              mount -t sysfs sys /sys
              mount -t devtmpfs dev /dev
              
              echo "71-Shard Monster System v0.1.0"
              echo "=============================="
              echo ""
              echo "Booting from 1.44MB floppy..."
              echo ""
              
              # Start shard 0
              ingest --shard 0 --port 7100 &
              
              echo "Shard 0 running on port 7100"
              echo "Ready for hash ingestion"
              echo ""
              
              exec /bin/sh
            ''; symlink = "/init"; }
        ];
        compressor = "gzip -9";
      };
      
      # Create bootable floppy image
      floppyImage = pkgs.stdenv.mkDerivation {
        name = "slackware-monster-floppy.img";
        nativeBuildInputs = [ pkgs.syslinux pkgs.dosfstools pkgs.mtools ];
        
        buildCommand = ''
          # Create 1.44MB floppy image
          dd if=/dev/zero of=floppy.img bs=1024 count=1440
          
          # Format as FAT12
          mkfs.vfat -F 12 -n "MONSTER71" floppy.img
          
          # Install syslinux bootloader
          syslinux --install floppy.img
          
          # Copy kernel and initramfs
          mcopy -i floppy.img ${kernel}/bzImage ::vmlinuz
          mcopy -i floppy.img ${initramfs}/initrd ::initrd.gz
          
          # Create syslinux config
          cat > syslinux.cfg <<EOF
          DEFAULT monster
          LABEL monster
            KERNEL vmlinuz
            APPEND initrd=initrd.gz quiet
          PROMPT 0
          TIMEOUT 10
          EOF
          
          mcopy -i floppy.img syslinux.cfg ::
          
          # Verify size
          SIZE=$(stat -c%s floppy.img)
          if [ $SIZE -gt 1474560 ]; then
            echo "ERROR: Image too large for floppy!"
            exit 1
          fi
          
          mv floppy.img $out
        '';
      };
      
    in {
      packages.${system} = {
        floppy = floppyImage;
        kernel = kernel;
        initramfs = initramfs;
        default = floppyImage;
      };
      
      apps.${system}.default = {
        type = "app";
        program = toString (pkgs.writeShellScript "run-floppy" ''
          ${pkgs.qemu}/bin/qemu-system-x86_64 \
            -m 64M \
            -fda ${floppyImage} \
            -boot a \
            -nographic
        '');
      };
    };
}
