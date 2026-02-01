#!/usr/bin/env bash
# Setup and run Tor reconnaissance

set -e

echo "🧅 Setting up Tor for reconnaissance..."

# Check if Tor is installed
if ! command -v tor &> /dev/null; then
    echo "❌ Tor not found. Installing..."
    if command -v apt-get &> /dev/null; then
        sudo apt-get update && sudo apt-get install -y tor
    elif command -v pacman &> /dev/null; then
        sudo pacman -S tor
    else
        echo "Please install Tor manually"
        exit 1
    fi
fi

# Start Tor service
echo "🔄 Starting Tor service..."
if systemctl is-active --quiet tor; then
    echo "✅ Tor already running"
else
    sudo systemctl start tor
    sleep 5
fi

# Verify Tor is listening
if netstat -tuln | grep -q ":9050"; then
    echo "✅ Tor SOCKS5 proxy active on 127.0.0.1:9050"
else
    echo "❌ Tor proxy not detected on port 9050"
    exit 1
fi

# Build and run reconnaissance
echo ""
echo "🔨 Building reconnaissance tool..."
cd shard0/recon
cargo build --release

echo ""
echo "🚀 Starting reconnaissance via Tor..."
cargo run --release

echo ""
echo "✅ Reconnaissance complete!"
echo "📄 Results saved to: challenge_recon_tor.json"
