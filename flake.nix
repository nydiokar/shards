{
  description = "TradeWars Science Lab - Reproducible Monster Group Analysis";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        
        # Python with science packages
        pythonEnv = pkgs.python311.withPackages (ps: with ps; [
          numpy scipy matplotlib pandas
          sympy networkx igraph
          z3-solver
          pytest hypothesis
        ]);
        
        # Rust with science crates
        rustEnv = pkgs.rustPlatform.buildRustPackage rec {
          pname = "monster-tools";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
        };
        
      in {
        # Development shells
        devShells = {
          # Full science lab
          default = pkgs.mkShell {
            name = "science-lab";
            buildInputs = with pkgs; [
              # Core tools
              bc jq graphviz imagemagick
              
              # Math systems
              gap pari maxima
              
              # Proof assistants
              lean4 coq z3 cvc5
              
              # Logic programming
              swiProlog
              
              # Lisp
              sbcl
              
              # Constraint solving
              minizinc
              
              # Languages
              pythonEnv
              rustc cargo
              
              # Build tools
              cmake pkg-config
            ];
            
            shellHook = ''
              echo "🔬 TradeWars Science Lab Loaded 🔬"
              echo "=================================="
              echo ""
              echo "Available tools:"
              echo "  Math: gap, pari, maxima"
              echo "  Proof: lean4, coq, z3, cvc5"
              echo "  Logic: swipl"
              echo "  Constraint: minizinc"
              echo "  Python: numpy, scipy, sympy, networkx"
              echo ""
              echo "∴ Reproducible science environment ✓"
            '';
          };
          
          # Minimal (proof + constraint only)
          minimal = pkgs.mkShell {
            buildInputs = with pkgs; [
              lean4 z3 minizinc
              bc jq
            ];
          };
          
          # Monster-specific (GAP + Lean4 + MiniZinc)
          monster = pkgs.mkShell {
            buildInputs = with pkgs; [
              gap lean4 minizinc z3
              pythonEnv
              bc jq graphviz
            ];
            
            shellHook = ''
              echo "🔷 Monster Group Analysis Environment 🔷"
              echo "GAP: Monster group computations"
              echo "Lean4: Formal proofs"
              echo "MiniZinc: Symmetry optimization"
              echo "Z3: SMT solving"
            '';
          };
        };
        
        # Packages
        packages = {
          # Science lab container
          scienceLabContainer = pkgs.dockerTools.buildImage {
            name = "tradewars-science-lab";
            tag = "latest";
            
            contents = with pkgs; [
              gap pari maxima
              lean4 coq z3 cvc5
              swiProlog sbcl
              minizinc
              pythonEnv
              bc jq graphviz
            ];
            
            config = {
              Cmd = [ "${pkgs.bash}/bin/bash" ];
              Env = [
                "PATH=/bin"
              ];
            };
          };
          
          # Buildkite pipeline
          buildkitePipeline = pkgs.writeText "pipeline.yml" ''
            steps:
              - label: "🔬 Science Lab Tests"
                command: |
                  nix develop .#default --command bash -c "
                    echo 'Testing GAP...'
                    gap --version
                    
                    echo 'Testing Lean4...'
                    lean --version
                    
                    echo 'Testing MiniZinc...'
                    minizinc --version
                    
                    echo 'Testing Z3...'
                    z3 --version
                    
                    echo '∴ All tools operational ✓'
                  "
              
              - label: "🔷 Monster Proofs"
                command: |
                  nix develop .#monster --command bash -c "
                    lake build
                    ./run_monster_tests.sh
                  "
              
              - label: "🌈 Maass Spectrum"
                command: |
                  nix develop .#default --command bash -c "
                    ./maass_spectrum_quick.sh
                    ./maass_spectrogram.sh
                  "
          '';
        };
        
        # Apps
        apps = {
          # Science lab shell
          lab = {
            type = "app";
            program = "${pkgs.writeShellScript "lab" ''
              exec ${pkgs.nix}/bin/nix develop ${self}#default
            ''}";
          };
          
          # Monster shell
          monster = {
            type = "app";
            program = "${pkgs.writeShellScript "monster" ''
              exec ${pkgs.nix}/bin/nix develop ${self}#monster
            ''}";
          };
        };
      }
    );
}
