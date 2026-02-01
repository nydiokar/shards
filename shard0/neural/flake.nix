{
  description = "Neural network for 71-shard pattern recognition";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ rust-overlay.overlays.default ];
      };
      rust = pkgs.rust-bin.stable.latest.default;
    in {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          rust cargo rustc
          pkg-config openssl
        ];
      };
    };
}
