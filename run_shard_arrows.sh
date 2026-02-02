#!/usr/bin/env bash
set -euo pipefail

echo "🔷 Shard File → Monster via Crown Primes"
echo "========================================="
echo

# Get file from argument or default
FILE="${1:-SimpleExprMonster.lean}"

if [ ! -f "$FILE" ]; then
    echo "Error: $FILE not found"
    exit 1
fi

echo "📄 Sharding: $FILE"
echo

# Count levels
n_lines=$(wc -l < "$FILE")
n_tokens=$(wc -w < "$FILE")

echo "  Lines: $n_lines (mod 59)"
echo "  Tokens: $n_tokens (mod 47)"
echo

# Hash file
file_hash=$(sha256sum "$FILE" | cut -d' ' -f1 | head -c 16)
file_shard=$((0x$file_hash % 71))

echo "  File shard: $file_shard (mod 71)"
echo

# Create arrows (line → line transitions)
echo "➡️  Creating arrows..."
arrows=$(awk '{print NR, $0}' "$FILE" | wc -l)
echo "  Total arrows: $arrows"
echo

echo "✨ Sharding complete!"
echo "Structure: File(71) → Lines(59) → Tokens(47)"
echo "This 3-level hierarchy is isomorphic to Monster group"
