{
  description = "Virtual device drivers for 71 shards";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        shard-lpt = pkgs.stdenv.mkDerivation {
          name = "shard-lpt";
          src = ./lpt;
          nativeBuildInputs = [ pkgs.kmod pkgs.linuxPackages.kernel.dev ];
          makeFlags = [
            "KERNELRELEASE=${pkgs.linuxPackages.kernel.modDirVersion}"
            "KERNEL_DIR=${pkgs.linuxPackages.kernel.dev}/lib/modules/${pkgs.linuxPackages.kernel.modDirVersion}/build"
          ];
          installPhase = ''
            mkdir -p $out/lib/modules/${pkgs.linuxPackages.kernel.modDirVersion}/extra
            cp shard_lpt.ko $out/lib/modules/${pkgs.linuxPackages.kernel.modDirVersion}/extra/
          '';
        };
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          linuxPackages.kernel.dev
          kmod
          gnumake
          gcc
        ];
        shellHook = ''
          echo "Kernel module development environment"
          echo "Build: cd shard0/drivers/lpt && make"
          echo "Load: sudo insmod shard_lpt.ko"
          echo "Test: echo 'Hello' > /dev/lpt0"
        '';
      };
    };
}
