{
  description = "Knowledge shard hasher";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    pipelight.url = "github:meta-introspector/pipelight";
  };

  outputs = { self, nixpkgs, pipelight }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages.${system}.default = pkgs.rustPlatform.buildRustPackage {
        pname = "shard-knowledge";
        version = "0.1.0";
        src = ./.;
        cargoLock.lockFile = ./Cargo.lock;
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          rustc
          cargo
          pipelight.packages.${system}.default or pipelight.defaultPackage.${system}
        ];
      };
    };
}
