#!/usr/bin/env bash
set -euo pipefail

echo "🔷 Shard All Files → 71 Shards"
echo "==============================="
echo

# Find all relevant files
LEAN_FILES=$(find . -name "*.lean" -type f 2>/dev/null | wc -l)
RUST_FILES=$(find . -name "*.rs" -type f 2>/dev/null | wc -l)
PYTHON_FILES=$(find . -name "*.py" -type f 2>/dev/null | wc -l)
MINIZINC_FILES=$(find . -name "*.mzn" -type f 2>/dev/null | wc -l)
HS_FILES=$(find . -name "*.hs" -type f 2>/dev/null | wc -l)
ORG_FILES=$(find . -name "*.org" -type f 2>/dev/null | wc -l)

TOTAL=$((LEAN_FILES + RUST_FILES + PYTHON_FILES + MINIZINC_FILES + HS_FILES + ORG_FILES))

echo "📊 File Inventory:"
echo "  Lean4:    $LEAN_FILES files"
echo "  Rust:     $RUST_FILES files"
echo "  Python:   $PYTHON_FILES files"
echo "  MiniZinc: $MINIZINC_FILES files"
echo "  Haskell:  $HS_FILES files"
echo "  Org:      $ORG_FILES files"
echo "  Total:    $TOTAL files"
echo

# Shard each file type
echo "🔷 Sharding by file type (mod 71):"

declare -A shards

# Process each file
for file in $(find . -type f \( -name "*.lean" -o -name "*.rs" -o -name "*.py" -o -name "*.mzn" -o -name "*.hs" -o -name "*.org" \) 2>/dev/null); do
    # Hash file content
    hash=$(sha256sum "$file" | cut -d' ' -f1 | head -c 16)
    shard=$((0x$hash % 71))
    
    # Count per shard
    shards[$shard]=$((${shards[$shard]:-0} + 1))
done

# Display distribution
echo
echo "📈 Shard Distribution (71 shards):"
for i in {0..70}; do
    count=${shards[$i]:-0}
    if [ $count -gt 0 ]; then
        bar=$(printf '█%.0s' $(seq 1 $count))
        printf "  Shard %2d: %3d files %s\n" $i $count "$bar"
    fi
done

echo
echo "✨ All files sharded into 71 shards!"
echo "Each shard corresponds to a Monster group element"
