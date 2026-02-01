{
  description = "Ham Radio software stack for CICADA-71 Morse Code Towers";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        hamradio = pkgs.buildEnv {
          name = "cicada71-hamradio";
          paths = with pkgs; [
            # Digital modes
            fldigi
            wsjt-x
            
            # Radio control
            hamlib
            chirp
            
            # APRS
            xastir
            direwolf
            
            # Logging
            cqrlog
            
            # SDR
            gnuradio
            gqrx
            rtl-sdr
            soapysdr
            
            # Satellite
            gpredict
            
            # Digital voice
            freedv
            codec2
            
            # Packet radio
            ax25-tools
            ax25-apps
            
            # Utilities
            multimon-ng
            rtl_433
          ];
        };
        
        default = self.packages.${system}.hamradio;
      };
      
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          fldigi
          wsjt-x
          hamlib
          gqrx
          direwolf
        ];
        
        shellHook = ''
          echo "📻 CICADA-71 Ham Radio Environment"
          echo "=================================="
          echo ""
          echo "71 Morse Code Towers"
          echo "23 Relay Nodes"
          echo "Monster Resonance: 9,936 Hz"
          echo ""
          echo "Available software:"
          echo "  fldigi   - Digital modes (PSK31, RTTY)"
          echo "  wsjt-x   - Weak signal (FT8, JT65)"
          echo "  gqrx     - SDR receiver"
          echo "  direwolf - Software TNC"
          echo ""
          echo "Frequency plan:"
          echo "  Shard 0-9:   3.5-4.0 MHz   (80m)"
          echo "  Shard 10-19: 7.0-7.3 MHz   (40m)"
          echo "  Shard 20-29: 14.0-14.35 MHz (20m)"
          echo "  Shard 30-39: 21.0-21.45 MHz (15m)"
          echo "  Shard 40-49: 28.0-29.7 MHz  (10m)"
          echo "  Shard 50-59: 144-148 MHz    (2m)"
          echo "  Shard 60-69: 420-450 MHz    (70cm)"
          echo "  Shard 70:    1296 MHz       (23cm - Moonbounce!)"
          echo ""
          echo "73 de M0NST 📡"
        '';
      };
    };
}
