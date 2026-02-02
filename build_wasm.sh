#!/usr/bin/env bash
# Build WASM module for browser

set -e

echo "🌐 Building WASM module..."

cd meme-detector

# Install wasm-pack if needed
if ! command -v wasm-pack &> /dev/null; then
    echo "📦 Installing wasm-pack..."
    cargo install wasm-pack
fi

# Build for web
wasm-pack build --target web --out-dir ../www/pkg

echo "✅ WASM module built: www/pkg/"
echo ""
echo "📊 Files generated:"
ls -lh ../www/pkg/

echo ""
echo "🚀 To test locally:"
echo "   cd www && python3 -m http.server 8000"
echo "   Open: http://localhost:8000/meme-emulator.html"
