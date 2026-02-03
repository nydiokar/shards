#!/usr/bin/env bash
# Generate zkTLS witnesses and Parquet shards

set -e

echo "🔐 zkTLS Witness Generator + RDFa Parquet Shards"
echo "=================================================="
echo ""

# Ensure Tor is running
if ! systemctl is-active --quiet tor; then
    echo "🧅 Starting Tor..."
    sudo systemctl start tor
    sleep 5
fi

# Build
echo "🔨 Building zkTLS generator..."
cd shard0/recon
cargo build --release --bin zktls

# Run
echo ""
echo "🚀 Generating zkTLS witnesses via Tor..."
cargo run --release --bin zktls

echo ""
echo "✅ Complete! Generated files:"
ls -lh shard*_zktls.parquet zktls_witnesses.json 2>/dev/null || true
