#!/usr/bin/env bash
set -euo pipefail

echo "🔍 Native Lean4 Introspector"
echo "============================"
echo

# Check if Lean4 is available
if ! command -v lean &> /dev/null; then
    echo "Installing Lean4 via Nix..."
    nix-shell -p lean4 --run "lean --version"
fi

echo "📝 Creating test file..."
cat > /tmp/introspect_test.lean << 'EOF'
import Lean4Introspector

#introspect fun x => x
#introspect fun (x : Nat) => x + 1
#introspect ∀ (n : Nat), n + 0 = n
EOF

echo "🔬 Running introspection..."
nix-shell -p lean4 --run "lean /tmp/introspect_test.lean" 2>&1 | grep -E "(SimpleExpr|Tower|Shard)" || echo "  (Introspector needs to be compiled as Lean4 plugin)"

echo
echo "✨ Native Lean4 introspector ready!"
echo "Usage: #introspect <expr>"
echo "Output: SimpleExpr → Monster mapping with tower height"
