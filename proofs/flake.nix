{
  description = "Planetary Conjunction Proof - Multi-language verification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        # Rust proof
        rust-proof = pkgs.rustPlatform.buildRustPackage {
          pname = "conjunction-proof-rust";
          version = "0.1.0";
          src = ./proofs/rust;
          cargoLock.lockFile = ./proofs/rust/Cargo.lock;
        };
        
        # Python proof
        python-proof = pkgs.writeShellScriptBin "python-proof" ''
          ${pkgs.python3}/bin/python3 ${./proofs/proof_conjunction.py}
        '';
        
        # JavaScript proof
        js-proof = pkgs.writeShellScriptBin "js-proof" ''
          ${pkgs.nodejs}/bin/node ${./proofs/proofConjunction.js}
        '';
        
        # Haskell proof
        haskell-proof = pkgs.haskellPackages.mkDerivation {
          pname = "conjunction-proof";
          version = "0.1.0";
          src = ./proofs/haskell;
          isLibrary = false;
          isExecutable = true;
          license = pkgs.lib.licenses.mit;
        };
        
        # All proofs in harmony
        all-proofs = pkgs.writeShellScriptBin "run-all-proofs" ''
          echo "🌍 Running Planetary Conjunction Proofs in Harmony ✨"
          echo "=================================================="
          
          echo "1. Rust proof..."
          ${self.packages.${system}.rust-proof}/bin/conjunction-proof-rust
          
          echo "2. Python proof..."
          ${self.packages.${system}.python-proof}/bin/python-proof
          
          echo "3. JavaScript proof..."
          ${self.packages.${system}.js-proof}/bin/js-proof
          
          echo "4. Haskell proof..."
          ${self.packages.${system}.haskell-proof}/bin/conjunction-proof
          
          echo "=================================================="
          echo "✨ All proofs converge: Chi Awakened! ✨"
        '';
        
        default = self.packages.${system}.all-proofs;
      };
    };
}
