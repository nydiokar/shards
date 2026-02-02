#!/usr/bin/env bash
# Pipelight pipeline for Lean ingestion

set -e

echo "🔧 Building Rust binary..."
cd ~/introspector/lean-ingest-gpu
cargo build --release

echo "🚀 Running ingestion..."
time ./target/release/lean-ingest-gpu

echo "📊 Stats..."
wc -l ~/introspector/lean_shards/*.json | tail -1
