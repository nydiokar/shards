{
  description = "ZX81 Rust with cassette tape bootloader";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      system = "x86_64-linux";
      overlays = [ rust-overlay.overlays.default ];
      pkgs = import nixpkgs { inherit system overlays; };
      
      rust = pkgs.rust-bin.stable.latest.default.override {
        extensions = [ "rust-src" ];
      };
    in {
      packages.${system} = {
        cassette-encoder = pkgs.rustPlatform.buildRustPackage {
          pname = "cassette-encoder";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          
          meta = {
            description = "ZX81 cassette tape audio encoder";
            license = pkgs.lib.licenses.agpl3;
          };
        };

        zx81-cicada = pkgs.stdenv.mkDerivation {
          pname = "zx81-cicada";
          version = "0.1.0";
          src = ./.;
          
          nativeBuildInputs = [
            rust
            pkgs.cargo
            pkgs.z88dk
            self.packages.${system}.cassette-encoder
          ];
          
          buildPhase = ''
            # Build cassette encoder first
            cargo build --release --bin cassette_encoder
            
            # Build ZX81 program (would need z80 target)
            # For now, use pre-built BASIC version
            cp level0.bas cicada-level0.bas
            
            # Convert BASIC to .P format
            z88dk-bas2tap -a10 -szx81 cicada-level0.bas
            
            # Generate cassette audio
            ./target/release/cassette_encoder cicada-level0.p cicada-level0.wav
          '';
          
          installPhase = ''
            mkdir -p $out/{bin,share/zx81}
            
            # Install encoder
            cp target/release/cassette_encoder $out/bin/
            
            # Install ZX81 files
            cp cicada-level0.bas $out/share/zx81/
            cp cicada-level0.p $out/share/zx81/
            cp cicada-level0.wav $out/share/zx81/
            
            # Install scripts
            cp build-cassette.sh $out/bin/
            chmod +x $out/bin/build-cassette.sh
          '';
          
          meta = {
            description = "CICADA-71 Level 0 for ZX81";
            license = pkgs.lib.licenses.agpl3;
          };
        };

        default = self.packages.${system}.zx81-cicada;
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rust
          pkgs.cargo
          pkgs.z88dk
          pkgs.zesarux
        ];
        
        shellHook = ''
          echo "🦀 ZX81 Rust Development Environment"
          echo "======================================"
          echo ""
          echo "Build cassette: ./build-cassette.sh"
          echo "Run emulator:   zesarux --machine ZX81"
          echo "Play audio:     aplay cicada-level0.wav"
          echo ""
          echo "Target: Z80 @ 3.25 MHz, 1KB RAM"
          echo "Audio: 1200 baud FSK, 44.1kHz WAV"
        '';
      };

      apps.${system} = {
        cassette-encoder = {
          type = "app";
          program = "${self.packages.${system}.cassette-encoder}/bin/cassette_encoder";
        };
        
        default = self.apps.${system}.cassette-encoder;
      };
    };
}
