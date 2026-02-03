#!/usr/bin/env bash
set -euo pipefail

echo "🔧 Maass Repair: Analyze File via Line→Token Arrows"
echo "====================================================="
echo

FILE="${1:-TestMeta.org}"

if [ ! -f "$FILE" ]; then
    echo "Error: $FILE not found"
    exit 1
fi

echo "Analyzing: $FILE"
echo

# File-level properties
total_lines=$(wc -l < "$FILE")
total_tokens=$(wc -w < "$FILE")
file_hash=$(sha256sum "$FILE" | cut -d' ' -f1 | head -c 16)
file_shard=$((0x$file_hash % 71))

echo "File-level:"
echo "  Lines: $total_lines"
echo "  Tokens: $total_tokens"
echo "  Shard: $file_shard (mod 71)"
echo

# Compute file-level Maass
file_lambda=$(echo "scale=4; 0.25 + ($total_lines / 71)^2" | bc)
echo "  Eigenvalue λ: $file_lambda"
echo

# Analyze line-by-line composition
echo "Line-level composition (first 20 lines):"
echo

line_num=0
declare -A line_shard_counts

while IFS= read -r line; do
    line_num=$((line_num + 1))
    
    if [ $line_num -le 20 ]; then
        # Line properties
        line_tokens=$(echo "$line" | wc -w)
        line_hash=$(echo "$line" | sha256sum | cut -d' ' -f1 | head -c 16)
        line_shard=$((0x$line_hash % 59))
        token_shard=$((line_tokens % 47))
        
        # Track line shard distribution
        line_shard_counts[$line_shard]=$((${line_shard_counts[$line_shard]:-0} + 1))
        
        printf "  Line %4d: shard(%2d,%2d) tokens=%3d\n" \
            "$line_num" "$line_shard" "$token_shard" "$line_tokens"
    fi
done < "$FILE"

echo
echo "Line shard distribution (all $total_lines lines):"

# Count all line shards
declare -A all_line_shards
line_num=0
while IFS= read -r line; do
    line_num=$((line_num + 1))
    line_hash=$(echo "$line" | sha256sum | cut -d' ' -f1 | head -c 16)
    line_shard=$((0x$line_hash % 59))
    all_line_shards[$line_shard]=$((${all_line_shards[$line_shard]:-0} + 1))
done < "$FILE"

# Show top 10 most common line shards
echo
for shard in $(for s in "${!all_line_shards[@]}"; do echo "$s ${all_line_shards[$s]}"; done | sort -k2 -rn | head -10); do
    shard_id=$(echo "$shard" | awk '{print $1}')
    count=$(echo "$shard" | awk '{print $2}')
    printf "  Shard %2d: %4d lines (%.1f%%)\n" "$shard_id" "$count" "$(echo "scale=1; $count * 100 / $total_lines" | bc)"
done

echo
echo "✨ Analysis complete!"
echo "High repair cost suggests lines are NOT well-composed"
echo "Lines spread across many shards → high entropy"
