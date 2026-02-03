#!/usr/bin/env bash
set -euo pipefail

echo "🔍 Find Duplicate Code via Monster Shards"
echo "=========================================="
echo

# Find all Lean4 files and hash their content
declare -A content_hashes
declare -A hash_files

echo "Scanning for duplicates..."

while IFS= read -r file; do
    if [ -f "$file" ]; then
        # Hash file content (not just filename)
        content_hash=$(sha256sum "$file" | cut -d' ' -f1)
        
        if [ -n "${hash_files[$content_hash]:-}" ]; then
            # Duplicate found!
            echo "  DUPLICATE:"
            echo "    $file"
            echo "    ${hash_files[$content_hash]}"
            
            # Show file sizes
            size1=$(wc -l < "$file")
            size2=$(wc -l < "${hash_files[$content_hash]}")
            echo "    Both: $size1 lines"
            echo
        else
            hash_files[$content_hash]="$file"
        fi
    fi
done < <(find . -name "*.lean" -type f 2>/dev/null)

# Find near-duplicates (same shard, similar size)
echo "Finding near-duplicates (same shard, similar size)..."
echo

declare -A shard_files

while IFS= read -r file; do
    if [ -f "$file" ]; then
        hash=$(sha256sum "$file" | cut -d' ' -f1 | head -c 16)
        shard=$((0x$hash % 71))
        lines=$(wc -l < "$file")
        
        shard_files["${shard}_${lines}"]="${shard_files[${shard}_${lines}]:-}|$file"
    fi
done < <(find . -name "*.lean" -type f 2>/dev/null)

# Report near-duplicates
for key in "${!shard_files[@]}"; do
    files="${shard_files[$key]}"
    count=$(echo "$files" | tr '|' '\n' | grep -c "^" || echo 0)
    
    if [ "$count" -gt 2 ]; then
        shard=$(echo "$key" | cut -d'_' -f1)
        lines=$(echo "$key" | cut -d'_' -f2)
        echo "  NEAR-DUPLICATE (Shard $shard, $lines lines):"
        echo "$files" | tr '|' '\n' | grep -v "^$" | head -5
        echo
    fi
done

echo "✨ Duplicate analysis complete!"
