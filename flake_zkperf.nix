{
  description = "zkPerf Monster System - Nix Flake";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        
        zkperf-monster = pkgs.rustPlatform.buildRustPackage {
          pname = "zkperf-monster";
          version = "0.1.0";
          
          src = ./.;
          
          cargoLock = {
            lockFile = ./Cargo.lock;
          };
          
          nativeBuildInputs = [ pkgs.rustc pkgs.cargo ];
          
          meta = {
            description = "zkPerf Monster Group System";
            license = pkgs.lib.licenses.cc0;
          };
        };
        
      in {
        packages = {
          default = zkperf-monster;
          zkperf-monster = zkperf-monster;
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.rustc
            pkgs.cargo
            pkgs.rust-analyzer
            pkgs.rustfmt
            pkgs.clippy
          ];
          
          shellHook = ''
            echo "🌀⚡ zkPerf Monster System"
            echo "========================="
            echo ""
            echo "Commands:"
            echo "  cargo build --bin zkperf-monster"
            echo "  cargo run --bin zkperf-monster"
            echo "  pipelight run zkperf"
            echo ""
          '';
        };
        
        apps.default = {
          type = "app";
          program = "${zkperf-monster}/bin/zkperf-monster";
        };
      }
    );
}
