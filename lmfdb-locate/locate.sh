#!/usr/bin/env bash
# Locate all LMFDB files and shard them into 71 projects

set -euo pipefail

echo "🔮⚡ LMFDB File Locator and Sharder"
echo ""

# Find all LMFDB files
echo "📂 Searching for LMFDB files..."
find /home/mdupont/experiments/monster -name "*lmfdb*" -type f 2>/dev/null > /tmp/lmfdb_all.txt || true
find /home/mdupont/introspector/monster -name "*lmfdb*" -type f 2>/dev/null >> /tmp/lmfdb_all.txt || true

total=$(wc -l < /tmp/lmfdb_all.txt)
echo "✅ Found $total files"
echo ""

# Categorize by extension
echo "📊 Categorizing by type..."
grep "\.json$" /tmp/lmfdb_all.txt > /tmp/lmfdb_json.txt || true
grep "\.parquet$" /tmp/lmfdb_all.txt > /tmp/lmfdb_parquet.txt || true
grep "\.md$" /tmp/lmfdb_all.txt > /tmp/lmfdb_md.txt || true
grep "\.py$" /tmp/lmfdb_all.txt > /tmp/lmfdb_py.txt || true
grep "\.rs$" /tmp/lmfdb_all.txt > /tmp/lmfdb_rs.txt || true

echo "  📊 JSON: $(wc -l < /tmp/lmfdb_json.txt)"
echo "  🗄️ Parquet: $(wc -l < /tmp/lmfdb_parquet.txt)"
echo "  📝 Markdown: $(wc -l < /tmp/lmfdb_md.txt)"
echo "  🐍 Python: $(wc -l < /tmp/lmfdb_py.txt)"
echo "  🦀 Rust: $(wc -l < /tmp/lmfdb_rs.txt)"
echo ""

# Shard into 71 buckets
echo "🔮 Sharding into 71 projects (mod 71)..."
awk '{shard = NR % 71; print shard, $0}' /tmp/lmfdb_all.txt > /tmp/lmfdb_sharded.txt

# Count files per shard
echo "📈 Files per shard:"
awk '{print $1}' /tmp/lmfdb_sharded.txt | sort -n | uniq -c | head -20

echo ""
echo "✅ Output files created:"
echo "  /tmp/lmfdb_all.txt - All files"
echo "  /tmp/lmfdb_sharded.txt - Sharded assignments"
echo "  /tmp/lmfdb_*.txt - By type"
