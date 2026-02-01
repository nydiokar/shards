#!/bin/bash
# build-cassette.sh - Build Rust and create ZX81 cassette tape audio

set -e

echo "🦀 Building Rust for ZX81..."

# Build cassette encoder
cargo build --release --bin cassette_encoder

# Build tape-to-URL encoder
cargo build --release --bin tape_to_url

# Build main program
cargo build --release --target z80-unknown-none

# Convert to ZX81 .P format
echo "📼 Creating ZX81 tape format..."
z88dk-appmake +zx81 \
    -b target/z80-unknown-none/release/zx81-rust \
    -o cicada-level0.p

# Check size
SIZE=$(stat -c%s cicada-level0.p 2>/dev/null || stat -f%z cicada-level0.p)
echo "Binary size: $SIZE bytes"

if [ $SIZE -gt 1024 ]; then
    echo "⚠️  WARNING: Binary larger than 1KB!"
fi

# Convert .P file to WAV audio (cassette tape format)
echo "🔊 Converting to cassette tape audio..."
./target/release/cassette_encoder cicada-level0.p cicada-level0.wav

# Encode to Gödel number URL
echo "🔢 Encoding to Gödel number URL..."
./target/release/tape_to_url cicada-level0.p

echo "✅ Cassette tape created!"
echo ""
echo "Files generated:"
echo "  cicada-level0.p      - ZX81 program file"
echo "  cicada-level0.wav    - Cassette tape audio (44.1kHz)"
echo "  cicada-level0.url    - Gödel-encoded URL with ZK proof"
echo "  cicada-level0.rdfa   - RDFa metadata"
echo ""
echo "Load in emulator: zesarux --machine ZX81 cicada-level0.p"
echo "Or play audio:    aplay cicada-level0.wav"
echo "Or visit URL:     cat cicada-level0.url"
