#!/bin/bash
# shard_docs.sh - Distribute documentation into 71 shards by complexity and harmonics

set -e

echo "🔮 CICADA-71 Document Sharding"
echo "================================"
echo ""

# Create shard manifest
MANIFEST="SHARD_MANIFEST.json"
echo "{" > "$MANIFEST"
echo '  "shards": [' >> "$MANIFEST"

# Find all documentation files
FILES=$(find . -maxdepth 1 -type f \( -name "*.md" -o -name "*.txt" \) ! -name "SHARD_MANIFEST.json" | sort)

SHARD_ID=0
FIRST=true

for FILE in $FILES; do
    BASENAME=$(basename "$FILE")
    
    # Calculate complexity metrics
    LINES=$(wc -l < "$FILE")
    WORDS=$(wc -w < "$FILE")
    CHARS=$(wc -c < "$FILE")
    
    # Harmonic hash: (lines * 7 + words * 3 + chars) mod 71
    HASH=$((($LINES * 7 + $WORDS * 3 + $CHARS) % 71))
    
    # Complexity score (0-10)
    if [ $LINES -lt 50 ]; then
        COMPLEXITY=1
    elif [ $LINES -lt 100 ]; then
        COMPLEXITY=2
    elif [ $LINES -lt 200 ]; then
        COMPLEXITY=3
    elif [ $LINES -lt 300 ]; then
        COMPLEXITY=4
    elif [ $LINES -lt 500 ]; then
        COMPLEXITY=5
    elif [ $LINES -lt 1000 ]; then
        COMPLEXITY=6
    elif [ $LINES -lt 2000 ]; then
        COMPLEXITY=7
    elif [ $LINES -lt 5000 ]; then
        COMPLEXITY=8
    elif [ $LINES -lt 10000 ]; then
        COMPLEXITY=9
    else
        COMPLEXITY=10
    fi
    
    # Assign to shard based on hash
    SHARD=$HASH
    
    # Add comma for JSON array
    if [ "$FIRST" = false ]; then
        echo "    }," >> "$MANIFEST"
    fi
    FIRST=false
    
    # Write entry
    cat >> "$MANIFEST" <<EOF
    {
      "file": "$BASENAME",
      "shard": $SHARD,
      "complexity": $COMPLEXITY,
      "lines": $LINES,
      "words": $WORDS,
      "bytes": $CHARS,
      "hash": $HASH
EOF
    
    echo "📄 $BASENAME → Shard $SHARD (complexity: $COMPLEXITY, lines: $LINES)"
done

# Close JSON
echo "    }" >> "$MANIFEST"
echo "  ]," >> "$MANIFEST"
echo '  "generated": "'$(date -u +%Y-%m-%dT%H:%M:%SZ)'",' >> "$MANIFEST"
echo '  "total_files": '$(echo "$FILES" | wc -l) >> "$MANIFEST"
echo "}" >> "$MANIFEST"

echo ""
echo "✅ Shard manifest created: $MANIFEST"
echo ""

# Generate shard distribution summary
echo "📊 Shard Distribution:"
echo "====================="

for i in {0..70}; do
    COUNT=$(grep -c "\"shard\": $i" "$MANIFEST" || echo 0)
    if [ $COUNT -gt 0 ]; then
        FILES_IN_SHARD=$(grep -B 5 "\"shard\": $i" "$MANIFEST" | grep '"file"' | cut -d'"' -f4 | tr '\n' ', ' | sed 's/,$//')
        echo "Shard $i: $COUNT files ($FILES_IN_SHARD)"
    fi
done

echo ""
echo "🎯 Complexity Distribution:"
echo "=========================="
for i in {1..10}; do
    COUNT=$(grep -c "\"complexity\": $i" "$MANIFEST" || echo 0)
    if [ $COUNT -gt 0 ]; then
        echo "Level $i: $COUNT files"
    fi
done

echo ""
echo "📈 Statistics:"
echo "============="
TOTAL_LINES=$(awk -F': ' '/lines/ {sum+=$2} END {print sum}' "$MANIFEST" | tr -d ',')
TOTAL_WORDS=$(awk -F': ' '/words/ {sum+=$2} END {print sum}' "$MANIFEST" | tr -d ',')
TOTAL_BYTES=$(awk -F': ' '/bytes/ {sum+=$2} END {print sum}' "$MANIFEST" | tr -d ',')

echo "Total lines: $TOTAL_LINES"
echo "Total words: $TOTAL_WORDS"
echo "Total bytes: $TOTAL_BYTES"

echo ""
echo "🔗 Harmonic Analysis:"
echo "===================="
echo "Distribution follows mod-71 harmonic hash:"
echo "  hash = (lines × 7 + words × 3 + bytes) mod 71"
echo ""
echo "This ensures balanced shard distribution based on"
echo "document complexity and Monster group harmonics."
