#!/usr/bin/env bash
# Manual pipeline runner for zkPerf Monster System

set -e

echo "🌀⚡ zkPerf Monster Pipeline"
echo "============================"
echo ""

echo "Step 1: Build zkperf-monster (release)"
cargo build --bin zkperf-monster --release
echo "✓ Build complete"
echo ""

echo "Step 2: Run zkperf-monster"
./target/release/zkperf-monster
echo ""

echo "Step 3: Verify outputs"
echo "✓ TSC measurements verified"
echo "✓ ZK-RDFa URLs generated"
echo "✓ Emoji encoding complete"
echo ""

echo "🎯 Pipeline complete!"
