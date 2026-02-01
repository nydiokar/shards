{
  description = "MMIX (Knuth's RISC) target for 71-shard Monster system";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      
      # MMIX toolchain (from Knuth's TAOCP)
      mmix = pkgs.stdenv.mkDerivation {
        name = "mmix";
        src = pkgs.fetchurl {
          url = "https://www-cs-faculty.stanford.edu/~knuth/programs/mmix-20131017.tar.gz";
          sha256 = "1hq8xpnkj9xjp5s5h8q8q8q8q8q8q8q8q8q8q8q8q8q8q8q8q8q8";
        };
        buildInputs = [ pkgs.gcc ];
        installPhase = ''
          mkdir -p $out/bin
          cp mmix mmixal mmmix mmotype $out/bin/
        '';
      };
      
      # Minimal shard for MMIX
      shardMMIX = pkgs.stdenv.mkDerivation {
        name = "shard-mmix";
        src = ./.;
        
        buildInputs = [ mmix ];
        
        buildPhase = ''
          # Compile MMIXAL assembly
          mmixal shard0.mms
        '';
        
        installPhase = ''
          mkdir -p $out/bin
          cp shard0.mmo $out/bin/
        '';
      };
      
    in {
      packages.${system} = {
        mmix-toolchain = mmix;
        shard-mmix = shardMMIX;
        default = shardMMIX;
      };
      
      apps.${system}.default = {
        type = "app";
        program = toString (pkgs.writeShellScript "run-mmix" ''
          ${mmix}/bin/mmix ${shardMMIX}/bin/shard0.mmo
        '');
      };
    };
}
