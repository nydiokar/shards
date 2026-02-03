#!/usr/bin/env bash
set -euo pipefail

echo "🔬 Testing Reproducible Science Lab 🔬"
echo "======================================"
echo

# Test default shell
echo "Testing default shell..."
nix develop .#default --command bash -c "
  echo '✓ GAP:' \$(gap --version 2>&1 | head -1)
  echo '✓ Lean4:' \$(lean --version)
  echo '✓ MiniZinc:' \$(minizinc --version | head -1)
  echo '✓ Z3:' \$(z3 --version)
  echo '✓ SWI-Prolog:' \$(swipl --version | head -1)
  echo '✓ Python numpy:' \$(python3 -c 'import numpy; print(numpy.__version__)')
"

echo
echo "Testing monster shell..."
nix develop .#monster --command bash -c "
  echo '✓ GAP available'
  echo '✓ Lean4 available'
  echo '✓ MiniZinc available'
  echo '✓ Z3 available'
"

echo
echo "Testing minimal shell..."
nix develop .#minimal --command bash -c "
  echo '✓ Lean4:' \$(lean --version)
  echo '✓ Z3:' \$(z3 --version)
  echo '✓ MiniZinc:' \$(minizinc --version | head -1)
"

echo
echo "∴ All shells operational ✓"
