{
  description = "71 Cryptanalysis Methods for Build Artifact Analysis";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
        };
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            rustToolchain
            cargo
            clippy
            rustfmt
            
            # Crypto analysis tools
            openssl
            libsodium
            
            # Performance tools
            perf-tools
            linuxPackages.perf
            valgrind
            
            # Binary analysis
            binutils
            radare2
            ghidra
            
            # Build tools
            pkg-config
            cmake
          ];
          
          RUST_BACKTRACE = "1";
          RUST_LOG = "debug";
        };

        packages.default = pkgs.rustPlatform.buildRustPackage {
          pname = "cryptanalysis-71";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
        };
      }
    );
}
