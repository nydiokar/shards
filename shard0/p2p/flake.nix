{
  description = "7-class P2P protocols for 71 shards";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    bitcoin.url = "github:bitcoin/bitcoin/v28.0";
    bitcoin.flake = false;
    solana.url = "github:anza-xyz/agave/v1.18.15";
    solana.flake = false;
    rust-libp2p.url = "github:libp2p/rust-libp2p/v0.54.1";
    rust-libp2p.flake = false;
    tor.url = "github:torproject/tor/tor-0.4.8.13";
    tor.flake = false;
  };

  outputs = { self, nixpkgs, bitcoin, solana, rust-libp2p, tor }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        bitcoind = pkgs.bitcoin.overrideAttrs { src = bitcoin; };
        
        solana-validator = pkgs.rustPlatform.buildRustPackage {
          pname = "solana-validator";
          version = "1.18.15";
          src = solana;
          cargoLock.lockFile = "${solana}/Cargo.lock";
          buildInputs = with pkgs; [ openssl pkg-config udev ];
        };
        
        libp2p-node = pkgs.rustPlatform.buildRustPackage {
          pname = "libp2p-node";
          version = "0.54.1";
          src = rust-libp2p;
          cargoLock.lockFile = "${rust-libp2p}/Cargo.lock";
        };
        
        tor = pkgs.tor.overrideAttrs { src = tor; };
        
        i2pd = pkgs.i2pd;
        
        ipfs = pkgs.kubo;
      };

      devShells.${system}.default = pkgs.mkShell {
        packages = with self.packages.${system}; [
          bitcoind
          solana-validator
          libp2p-node
          tor
          i2pd
          ipfs
        ] ++ (with pkgs; [
          # Wireless sneakernet
          bluez
          bluez-tools
          obexftp
          batctl
          iw
          # Steganography
          steghide
          outguess
          stegsolve
          qrencode
          zbar
          imagemagick
        ]);
        
        shellHook = ''
          echo "7-class P2P protocols + sneakernet ready:"
          echo "  Class 0: bitcoind -regtest -daemon"
          echo "  Class 1: solana-test-validator"
          echo "  Class 2: libp2p-node"
          echo "  Class 3: tor"
          echo "  Class 4: i2pd"
          echo "  Class 5: ipfs daemon"
          echo "  Class 6: dead drops at /nix/store/shard*-deaddrop/"
          echo ""
          echo "Sneakernet extensions:"
          echo "  Bluetooth: bluetoothctl, obexftp"
          echo "  WiFi Mesh: iw, batctl"
          echo "  Stego: steghide, qrencode"
        '';
      };
    };
}
