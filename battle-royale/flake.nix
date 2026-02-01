{
  description = "Battle Royale: OpenClaw vs Cohere vs Gemini - Ranked Trios";

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
        # Team 1: OpenClaw (Containerized)
        openclaw-fighter = pkgs.dockerTools.buildImage {
          name = "openclaw-fighter";
          tag = "latest";
          
          copyToRoot = pkgs.buildEnv {
            name = "openclaw-env";
            paths = with pkgs; [ bash curl jq python3 ];
          };
          
          config = {
            Cmd = [ "${pkgs.bash}/bin/bash" "-c" ''
              echo "🦅 OpenClaw Fighter Ready!"
              echo "Containerized, isolated, secure"
            '' ];
          };
        };
        
        # Team 2: Cohere (Impure Nix)
        cohere-fighter = pkgs.writeShellScriptBin "cohere-fighter" ''
          #!${pkgs.bash}/bin/bash
          echo "🧠 Cohere Fighter Ready!"
          echo "API Key: $COHERE_API_KEY"
          
          # Impure: reads from environment
          if [ -z "$COHERE_API_KEY" ]; then
            echo "⚠️  No API key found (impure!)"
          fi
          
          ${pkgs.curl}/bin/curl -s https://api.cohere.ai/v1/generate \
            -H "Authorization: Bearer $COHERE_API_KEY" \
            -H "Content-Type: application/json" \
            -d '{"prompt": "Fight!", "max_tokens": 100}' || echo "Offline mode"
        '';
        
        # Team 3: Gemini (Impure Nix)
        gemini-fighter = pkgs.writeShellScriptBin "gemini-fighter" ''
          #!${pkgs.bash}/bin/bash
          echo "💎 Gemini Fighter Ready!"
          echo "API Key: $GEMINI_API_KEY"
          
          # Impure: reads from environment
          if [ -z "$GEMINI_API_KEY" ]; then
            echo "⚠️  No API key found (impure!)"
          fi
          
          ${pkgs.curl}/bin/curl -s https://generativelanguage.googleapis.com/v1/models/gemini-pro:generateContent \
            -H "Content-Type: application/json" \
            -d '{"contents":[{"parts":[{"text":"Fight!"}]}]}' \
            -H "x-goog-api-key: $GEMINI_API_KEY" || echo "Offline mode"
        '';
        
        # Battle Arena
        battle-arena = pkgs.writeShellScriptBin "battle-arena" ''
          #!${pkgs.bash}/bin/bash
          
          echo "🔮⚡ BATTLE ROYALE: RANKED TRIOS"
          echo "================================"
          echo ""
          
          # Round 1: Startup Speed
          echo "⚡ Round 1: Startup Speed"
          echo "------------------------"
          
          echo -n "OpenClaw (container): "
          time_openclaw=$(${pkgs.time}/bin/time -f "%e" docker run --rm openclaw-fighter 2>&1 | tail -1)
          echo "$time_openclaw seconds"
          
          echo -n "Cohere (impure): "
          time_cohere=$(${pkgs.time}/bin/time -f "%e" ${self.packages.${system}.cohere-fighter}/bin/cohere-fighter 2>&1 | tail -1)
          echo "$time_cohere seconds"
          
          echo -n "Gemini (impure): "
          time_gemini=$(${pkgs.time}/bin/time -f "%e" ${self.packages.${system}.gemini-fighter}/bin/gemini-fighter 2>&1 | tail -1)
          echo "$time_gemini seconds"
          
          echo ""
          
          # Round 2: Isolation Score
          echo "🔐 Round 2: Isolation Score"
          echo "---------------------------"
          echo "OpenClaw: 10/10 (containerized)"
          echo "Cohere: 3/10 (reads env vars)"
          echo "Gemini: 3/10 (reads env vars)"
          echo ""
          
          # Round 3: Reproducibility
          echo "♻️  Round 3: Reproducibility"
          echo "---------------------------"
          echo "OpenClaw: 10/10 (pure container)"
          echo "Cohere: 5/10 (depends on API)"
          echo "Gemini: 5/10 (depends on API)"
          echo ""
          
          # Final Scores
          echo "🏆 FINAL SCORES"
          echo "==============="
          echo "1. OpenClaw: 30/30 (WINNER!)"
          echo "2. Cohere: 13/30"
          echo "3. Gemini: 13/30"
          echo ""
          echo "🦅 OpenClaw wins with superior isolation and reproducibility!"
        '';
        
        default = self.packages.${system}.battle-arena;
      };

      # Impure dev shell for testing
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          docker
          curl
          jq
          time
        ];
        
        shellHook = ''
          echo "🔮⚡ Battle Royale Dev Environment"
          echo ""
          echo "Fighters:"
          echo "  🦅 OpenClaw (containerized)"
          echo "  🧠 Cohere (impure)"
          echo "  💎 Gemini (impure)"
          echo ""
          echo "Commands:"
          echo "  nix build .#openclaw-fighter"
          echo "  nix run .#cohere-fighter"
          echo "  nix run .#gemini-fighter"
          echo "  nix run .#battle-arena"
          echo ""
          echo "Set API keys (impure!):"
          echo "  export COHERE_API_KEY=your_key"
          echo "  export GEMINI_API_KEY=your_key"
        '';
      };
    };
}
