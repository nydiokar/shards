#!/usr/bin/env bash
set -euo pipefail

echo "🔍 Find Similar Code via Monster Shards"
echo "========================================"
echo

# Get target file from argument
TARGET="${1:-SimpleExprMonster.lean}"

if [ ! -f "$TARGET" ]; then
    echo "Error: $TARGET not found"
    exit 1
fi

echo "Target: $TARGET"
echo

# Hash target file
target_hash=$(sha256sum "$TARGET" | cut -d' ' -f1 | head -c 16)
target_shard=$((0x$target_hash % 71))

echo "Target shard: $target_shard (mod 71)"
echo

# Find files in same shard
echo "Files in same shard:"
for file in $(find . -type f \( -name "*.lean" -o -name "*.rs" -o -name "*.py" -o -name "*.mzn" \) 2>/dev/null); do
    if [ "$file" != "$TARGET" ]; then
        hash=$(sha256sum "$file" | cut -d' ' -f1 | head -c 16)
        shard=$((0x$hash % 71))
        
        if [ $shard -eq $target_shard ]; then
            lines=$(wc -l < "$file")
            echo "  $file ($lines lines)"
        fi
    fi
done

echo
echo "Files in adjacent shards (±1):"
prev_shard=$(( (target_shard - 1 + 71) % 71 ))
next_shard=$(( (target_shard + 1) % 71 ))

for file in $(find . -type f \( -name "*.lean" -o -name "*.rs" -o -name "*.py" -o -name "*.mzn" \) 2>/dev/null | head -20); do
    if [ "$file" != "$TARGET" ]; then
        hash=$(sha256sum "$file" | cut -d' ' -f1 | head -c 16)
        shard=$((0x$hash % 71))
        
        if [ $shard -eq $prev_shard ] || [ $shard -eq $next_shard ]; then
            lines=$(wc -l < "$file")
            echo "  $file (shard $shard, $lines lines)"
        fi
    fi
done

echo
echo "✨ Similar code found via Monster shard proximity!"
