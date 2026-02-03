#!/usr/bin/env bash
# Build Bisque for WASM + Node.js

set -euo pipefail

echo "🦞 Building Bisque WASM..."

# Install wasm-pack if needed
if ! command -v wasm-pack &> /dev/null; then
    cargo install wasm-pack
fi

# Build for Node.js
cd shard58/bisque
wasm-pack build --target nodejs --out-dir pkg

echo "✅ Bisque WASM built: shard58/bisque/pkg/"
echo ""
echo "Usage in Node.js:"
echo "  const bisque = require('./shard58/bisque/pkg');"
echo "  const client = new bisque.BisqueWasm();"
echo "  const response = await client.fetch('https://example.com');"
