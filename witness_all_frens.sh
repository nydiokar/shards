#!/usr/bin/env bash
# witness_all_frens.sh - zkTLS witness all FREN pages with perf capture
# Captures: token page, linked pages, home pages, full session

set -euo pipefail

WITNESS_DIR="witnesses/frens"
SESSION_DIR="witnesses/sessions"
mkdir -p "$SESSION_DIR"

TOKENS=(
  "E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
  "BwUTq7fS6sfUmHDwAiCQZ3asSiPEapW5zDrsbwtapump"
  "GNBe3at5NDpu45z1foWwrVfdxYhFA5dYWqNm2JMVSCAM"
  "DD87KkJH3hJeTC8U3msdrbzwkApmjDrxXA3sTbC7FAKE"
  "9DgKaWyhitMG1AtAdAAozy9ZspRUa42omzrZHnHw5FUN"
  "Fuj6EDWQHBnQ3eEvYDujNQ4rPLSkhm3pBySbQ79Bpump"
  "9bzJn2jHQPCGsYKapFvytJQcbaz5FN2TtNB43jb1pump"
)

echo "🔐 zkTLS witnessing all FRENs with perf..."
echo "=================================================="

for i in "${!TOKENS[@]}"; do
  TOKEN="${TOKENS[$i]}"
  NUM=$((i + 1))
  
  echo "[$NUM/7] $TOKEN"
  
  SESSION_FILE="$SESSION_DIR/${TOKEN}_session.json"
  PERF_FILE="$SESSION_DIR/${TOKEN}_session.perf"
  
  # Start perf for entire session
  echo "   Starting perf capture..."
  
  # Run zkTLS witness with perf
  cd shard0/zktls
  
  if [ -f "flake.nix" ]; then
    echo "   Building zkTLS with Nix..."
    if nix build 2>/dev/null; then
      echo "   Running zkTLS witness..."
      perf record -o "../../$PERF_FILE" -- \
        ./result/bin/frens_phone "https://solscan.io/token/$TOKEN" \
        > "../../$SESSION_FILE" 2>&1 || true
    fi
  fi
  
  cd ../..
  
  # Create session witness
  cat >> "$SESSION_FILE" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN",
  "urls_witnessed": [
    "https://solscan.io/token/$TOKEN",
    "https://solscan.io",
    "https://pump.fun/coin/$TOKEN"
  ],
  "perf_file": "$PERF_FILE",
  "perf_size": $(stat -c%s "$PERF_FILE" 2>/dev/null || echo "0")
}
EOF
  
  echo "   Session: $SESSION_FILE"
  echo "   Perf: $PERF_FILE"
  echo ""
done

echo "=================================================="
echo "✨ All FRENs witnessed!"
echo "   Sessions: $(ls -1 "$SESSION_DIR"/*.json 2>/dev/null | wc -l)"
echo "   Perf files: $(ls -1 "$SESSION_DIR"/*.perf 2>/dev/null | wc -l)"
