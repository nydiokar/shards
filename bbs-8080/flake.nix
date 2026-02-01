{
  description = "8080 BBS Server - 16-bit Perfect Architecture";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages.${system} = {
        bbs-8080 = pkgs.rustPlatform.buildRustPackage {
          pname = "bbs-8080";
          version = "0.1.0";
          
          src = ./.;
          
          cargoLock = {
            lockFile = ./Cargo.lock;
          };
          
          meta = {
            description = "8080 BBS Server - 16-bit Perfect Architecture";
          };
        };
        
        default = self.packages.${system}.bbs-8080;
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          rustc
          cargo
          rust-analyzer
        ];
        
        shellHook = ''
          echo "🔮⚡ 8080 BBS Server Development"
          echo ""
          echo "Architecture:"
          echo "  16-bit address space (0x0000 - 0xFFFF)"
          echo "  8080 port (Intel 8080 tribute)"
          echo "  71 shards (mod 71 routing)"
          echo "  Power-by-power memory layout"
          echo ""
          echo "Commands:"
          echo "  cargo build"
          echo "  cargo run"
        '';
      };
    };
}
