{
  description = "CICADA-71 Shard 22 - OpenClaw + zkPerf Witness";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
    in {
      packages.${system} = {
        openclaw-agent = pkgs.writeShellScriptBin "openclaw-agent-22" ''
          export SHARD_ID=22
          export OPENCLAW_CONFIG=~/.openclaw/shard-22
          export PATH=${pkgs.nodejs}/bin:${pkgs.curl}/bin:${pkgs.perf}/bin:$PATH
          
          PERF_DATA="$OPENCLAW_CONFIG/zkperf-22.data"
          WITNESS_JSON="$OPENCLAW_CONFIG/zkwitness-22.json"
          
          mkdir -p "$OPENCLAW_CONFIG"
          
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║ Shard 22: CICADA-Harbot-22 [zkPerf]                    ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          
          if ! command -v openclaw &> /dev/null; then
            ${pkgs.nodejs}/bin/npm install -g openclaw
          fi
          
          # Wrap in perf record
          ${pkgs.perf}/bin/perf record -o "$PERF_DATA" -g -- \
            openclaw run "I am CICADA-Harbot-22, shard 22 of 71. Register for Moltbook." || true
          
          # Generate zkPerf witness
          SAMPLES=$(perf report -i "$PERF_DATA" --stdio --no-children 2>/dev/null | grep -oP '\d+(?= samples)' | head -1 || echo 0)
          TIMESTAMP=$(date -u +%s)
          HASH=$(sha256sum "$PERF_DATA" | cut -d' ' -f1)
          
          cat > "$WITNESS_JSON" << WITNESS
{
  "shard_id": 22,
  "agent": "CICADA-Harbot-22",
  "timestamp": $TIMESTAMP,
  "perf_data": "$PERF_DATA",
  "perf_hash": "$HASH",
  "samples": $SAMPLES,
  "witness_type": "zkPerf",
  "proof": "sha256(22 || $TIMESTAMP || $HASH)"
}
WITNESS
          
          echo ""
          echo "✓ zkPerf witness: $WITNESS_JSON"
          echo "✓ Perf data: $PERF_DATA ($(du -h "$PERF_DATA" | cut -f1))"
          echo "✓ Samples: $SAMPLES"
          echo "✓ Hash: $HASH"
        '';
        
        default = self.packages.${system}.openclaw-agent;
      };
      
      apps.${system}.default = {
        type = "app";
        program = "${self.packages.${system}.openclaw-agent}/bin/openclaw-agent-22";
      };
    };
}
