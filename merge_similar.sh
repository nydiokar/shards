#!/usr/bin/env bash
set -euo pipefail

echo "🔀 Merge Similar Code via Monster Shards"
echo "========================================="
echo

TARGET="${1:-SimpleExprMonster.lean}"

echo "Finding mergeable code for: $TARGET"
echo

# Find similar Lean files in same shard
similar_files=$(./find_similar.sh "$TARGET" 2>/dev/null | grep "\.lean" | grep -v "^Target:" | awk '{print $1}')

echo "Mergeable candidates:"
for file in $similar_files; do
    if [ -f "$file" ] && [ "$file" != "$TARGET" ]; then
        lines=$(wc -l < "$file")
        
        # Check for common imports
        common_imports=$(grep -h "^import" "$TARGET" "$file" 2>/dev/null | sort | uniq -d | wc -l)
        
        # Check for common namespaces
        common_ns=$(grep -h "^namespace" "$TARGET" "$file" 2>/dev/null | sort | uniq -d | wc -l)
        
        if [ $common_imports -gt 0 ] || [ $common_ns -gt 0 ]; then
            echo "  ✓ $file ($lines lines, $common_imports common imports, $common_ns common namespaces)"
        else
            echo "    $file ($lines lines)"
        fi
    fi
done

echo
echo "Suggested merge:"
echo "  MonsterMerged.lean ← SimpleExprMonster + maass_forms + motives"
echo
echo "✨ Use MonsterMerged.lean for unified Monster structure"
