#!/usr/bin/env bash
# Run agent evaluation in Rust

set -e

SHARD_ID=${1:-0}

echo "🎯 Evaluating all agents on shard $SHARD_ID (Rust)"
echo "=================================================="
echo ""

# Build once
echo "🔨 Building evaluator..."
cd agents/evaluate
cargo build --release
cd ../..

FRAMEWORKS=("claude" "openai" "ollama")

for fw in "${FRAMEWORKS[@]}"; do
    echo "🤖 Testing $fw..."
    ./agents/evaluate/target/release/evaluate --framework "$fw" --shard "$SHARD_ID" || echo "   ⚠️  $fw failed"
    echo ""
done

echo "📊 Generating leaderboard..."
cd agents/leaderboard
cargo build --release
cargo run --release
cd ../..

echo ""
echo "✅ Evaluation complete!"
echo "📄 Results in: results/"
echo "📊 Leaderboard: LEADERBOARD.md"
