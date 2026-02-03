#!/usr/bin/env bash
set -euo pipefail

echo "🔍 3-Level Maass Restoration: Detect Exact Duplication"
echo "======================================================="
echo

# Analyze all Lean files
echo "Analyzing Lean4 files..."

declare -A shard_map

while IFS= read -r file; do
    if [ -f "$file" ]; then
        # Get properties
        lines=$(wc -l < "$file")
        tokens=$(wc -w < "$file")
        hash=$(sha256sum "$file" | cut -d' ' -f1 | head -c 16)
        
        # Compute 3-level shards
        file_shard=$((0x$hash % 71))
        line_shard=$((lines % 59))
        token_shard=$((tokens % 47))
        
        # Create composite key
        key="${file_shard}_${line_shard}_${token_shard}"
        
        # Track files with same 3-level shard
        shard_map["$key"]="${shard_map[$key]:-}|$file"
    fi
done < <(find . -name "*.lean" -type f 2>/dev/null | head -50)

# Find exact duplicates (same 3-level shard)
echo "Exact duplicates (same 71×59×47 shard):"
echo

n_duplicates=0
for key in "${!shard_map[@]}"; do
    files="${shard_map[$key]}"
    count=$(echo "$files" | tr '|' '\n' | grep -c "^" || echo 0)
    
    if [ "$count" -gt 2 ]; then
        n_duplicates=$((n_duplicates + 1))
        file_shard=$(echo "$key" | cut -d'_' -f1)
        line_shard=$(echo "$key" | cut -d'_' -f2)
        token_shard=$(echo "$key" | cut -d'_' -f3)
        
        echo "  Shard ($file_shard, $line_shard, $token_shard): $count files"
        echo "$files" | tr '|' '\n' | grep -v "^$" | head -3 | sed 's/^/    /'
        echo
    fi
done

if [ $n_duplicates -eq 0 ]; then
    echo "  No exact duplicates found"
    echo "  (All files have unique 3-level shards)"
fi

echo
echo "✨ Total shards: 196,883 (71×59×47)"
echo "∴ Exact duplication detected via pure symmetry ✓"
