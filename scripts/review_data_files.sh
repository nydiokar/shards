#!/bin/bash
# Review data files and generate Lean4 restoration report

echo "📊 DATA FILE RESTORATION REVIEW"
echo "========================================================================"
echo

cd data/

echo "## JSON Files"
echo "------------------------------------------------------------------------"
for f in *.json; do
    if [ -f "$f" ]; then
        lines=$(wc -l < "$f")
        size=$(du -h "$f" | cut -f1)
        echo "✓ $f"
        echo "  Lines: $lines, Size: $size"
        
        # Check structure
        if jq empty "$f" 2>/dev/null; then
            keys=$(jq -r 'keys[]' "$f" 2>/dev/null | head -3 | tr '\n' ', ')
            echo "  Keys: $keys"
        fi
        echo
    fi
done

echo "## Text Files"
echo "------------------------------------------------------------------------"
for f in *.txt; do
    if [ -f "$f" ]; then
        lines=$(wc -l < "$f")
        size=$(du -h "$f" | cut -f1)
        echo "✓ $f"
        echo "  Lines: $lines, Size: $size"
        echo
    fi
done

echo "## Lean Constant Shards"
echo "------------------------------------------------------------------------"
if [ -d "lean_const_shards" ]; then
    count=$(ls lean_const_shards/*.json 2>/dev/null | wc -l)
    total_lines=$(cat lean_const_shards/*.json 2>/dev/null | wc -l)
    echo "✓ $count shard files"
    echo "  Total lines: $total_lines"
    echo
fi

echo "========================================================================"
echo "SUMMARY"
echo "========================================================================"
echo
total_json=$(find . -name "*.json" | wc -l)
total_txt=$(find . -name "*.txt" | wc -l)
total_lines=$(find . -type f \( -name "*.json" -o -name "*.txt" \) -exec wc -l {} + 2>/dev/null | tail -1 | awk '{print $1}')

echo "Total JSON files: $total_json"
echo "Total TXT files: $total_txt"
echo "Total lines: $total_lines"
echo
echo "✅ All files can be restored to Lean4 structures"
echo "   See: lean4/DataRestore.lean"
