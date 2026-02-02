{
  description = "CICADA-71 Complete Proof System - Pure Nix + zkPerf";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" ];
          targets = [ "wasm32-unknown-unknown" "wasm32-wasi" ];
        };
      in
      {
        packages = {
          # Rust rewrite of Python components
          harbot-core = pkgs.rustPlatform.buildRustPackage {
            pname = "harbot-core";
            version = "0.1.0";
            src = ./rust-core;
            cargoLock.lockFile = ./rust-core/Cargo.lock;
            nativeBuildInputs = [ rustToolchain pkgs.linuxPackages.perf ];
          };

          # WASM build
          harbot-wasm = pkgs.rustPlatform.buildRustPackage {
            pname = "harbot-wasm";
            version = "0.1.0";
            src = ./rust-core;
            cargoLock.lockFile = ./rust-core/Cargo.lock;
            nativeBuildInputs = [ rustToolchain pkgs.wasm-pack ];
            buildPhase = ''
              wasm-pack build --target web --out-dir $out
            '';
          };

          # Lean4 proofs
          harbot-lean = pkgs.stdenv.mkDerivation {
            pname = "harbot-lean";
            version = "0.1.0";
            src = ./lean-proofs;
            buildInputs = [ pkgs.lean4 ];
            buildPhase = ''
              lake build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r .lake/build $out/
            '';
          };

          # Coq proofs
          harbot-coq = pkgs.coqPackages.mkCoqDerivation {
            pname = "harbot-coq";
            version = "0.1.0";
            src = ./coq-proofs;
            buildInputs = [ pkgs.coq ];
          };

          # Prolog proofs
          harbot-prolog = pkgs.stdenv.mkDerivation {
            pname = "harbot-prolog";
            version = "0.1.0";
            src = ./prolog-proofs;
            buildInputs = [ pkgs.swiProlog ];
            installPhase = ''
              mkdir -p $out/bin
              cp *.pl $out/bin/
            '';
          };

          # MiniZinc optimization
          harbot-minizinc = pkgs.stdenv.mkDerivation {
            pname = "harbot-minizinc";
            version = "0.1.0";
            src = ./minizinc-models;
            buildInputs = [ pkgs.minizinc ];
            installPhase = ''
              mkdir -p $out/models
              cp *.mzn $out/models/
            '';
          };

          # zkPerf witness generator
          zkperf-witness = pkgs.writeShellScriptBin "zkperf-witness" ''
            set -e
            PROOF_DIR="./zkperf_proofs"
            mkdir -p "$PROOF_DIR"
            
            echo "🔮 Generating zkPerf witnesses for all components..."
            
            # Build Rust with perf
            perf record -o "$PROOF_DIR/rust_build.perf.data" -g -- \
              ${pkgs.cargo}/bin/cargo build --release
            
            # Run tests with perf
            perf record -o "$PROOF_DIR/rust_test.perf.data" -g -- \
              ${pkgs.cargo}/bin/cargo test
            
            # Build WASM with perf
            perf record -o "$PROOF_DIR/wasm_build.perf.data" -g -- \
              ${pkgs.wasm-pack}/bin/wasm-pack build --target web
            
            # Verify Lean4 proofs with perf
            perf record -o "$PROOF_DIR/lean_verify.perf.data" -g -- \
              ${pkgs.lean4}/bin/lake build
            
            # Verify Coq proofs with perf
            perf record -o "$PROOF_DIR/coq_verify.perf.data" -g -- \
              ${pkgs.coq}/bin/coqc *.v
            
            # Run Prolog proofs with perf
            perf record -o "$PROOF_DIR/prolog_verify.perf.data" -g -- \
              ${pkgs.swiProlog}/bin/swipl -g main -t halt *.pl
            
            # Solve MiniZinc models with perf
            perf record -o "$PROOF_DIR/minizinc_solve.perf.data" -g -- \
              ${pkgs.minizinc}/bin/minizinc *.mzn
            
            echo "✅ All zkPerf witnesses generated"
            ls -lh "$PROOF_DIR"
          '';

          default = self.packages.${system}.harbot-core;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            rustToolchain
            pkgs.cargo
            pkgs.rustc
            pkgs.wasm-pack
            pkgs.lean4
            pkgs.coq
            pkgs.swiProlog
            pkgs.minizinc
            pkgs.linuxPackages.perf
            pkgs.python3
            pkgs.nodejs
          ];
        };
      }
    );
}
