{
  description = "TradeWars 71 - Navigate to Sgr A* using j-invariant";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        packages = {
          tradewars71 = pkgs.rustPlatform.buildRustPackage {
            pname = "tradewars71";
            version = "0.1.0";
            
            src = ./.;
            
            cargoLock = {
              lockFile = ./Cargo.lock;
            };
            
            nativeBuildInputs = with pkgs; [ rustc cargo ];
            
            meta = with pkgs.lib; {
              description = "TradeWars 71: Navigate to Sgr A* using j-invariant";
              license = licenses.cc0;
            };
          };
          
          default = self.packages.${system}.tradewars71;
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            rustc
            cargo
            rust-analyzer
            clippy
            rustfmt
          ];
          
          shellHook = ''
            echo "🐓🦅👹 TradeWars 71 Development Environment"
            echo "Commands:"
            echo "  cargo build --release --bin tradewars71"
            echo "  cargo run --bin tradewars71"
            echo "  ./target/release/tradewars71"
          '';
        };
      }
    );
}
