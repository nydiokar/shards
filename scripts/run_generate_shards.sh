#!/usr/bin/env bash
# Generate all 497 shard challenges with ZK proof templates

set -e

echo "🔨 71-Shard Challenge Generator"
echo "================================"
echo ""

cd shard0/recon

echo "📦 Building generator..."
cargo build --release --bin generate-shards

echo ""
echo "🚀 Generating 497 shards..."
cargo run --release --bin generate-shards

echo ""
echo "✅ Complete! Generated files:"
ls -lh shard_challenges.json zk_proof_templates.json 2>/dev/null || true

echo ""
echo "📊 Preview:"
head -20 shard_challenges.json
