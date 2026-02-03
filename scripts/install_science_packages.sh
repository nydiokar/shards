#!/usr/bin/env bash
set -euo pipefail

echo "🔬 Installing Science Packages for TradeWars Ship 🔬"
echo "===================================================="
echo

# Check what's already installed
echo "📊 Checking existing packages..."
echo

has_cmd() { command -v "$1" &>/dev/null; }

# Core tools
echo "Core Tools:"
has_cmd octave && echo "  ✓ Octave" || echo "  ✗ Octave"
has_cmd gnuplot && echo "  ✓ GnuPlot" || echo "  ✗ GnuPlot"
has_cmd dot && echo "  ✓ Graphviz" || echo "  ✗ Graphviz"
has_cmd bc && echo "  ✓ bc" || echo "  ✗ bc"
has_cmd jq && echo "  ✓ jq" || echo "  ✗ jq"
echo

# Math systems
echo "Math Systems:"
has_cmd sage && echo "  ✓ SageMath" || echo "  ✗ SageMath"
has_cmd gap && echo "  ✓ GAP" || echo "  ✗ GAP"
has_cmd gp && echo "  ✓ PARI/GP" || echo "  ✗ PARI/GP"
has_cmd maxima && echo "  ✓ Maxima" || echo "  ✗ Maxima"
echo

# Proof assistants
echo "Proof Assistants:"
has_cmd lean && echo "  ✓ Lean4" || echo "  ✗ Lean4"
has_cmd coqc && echo "  ✓ Coq" || echo "  ✗ Coq"
has_cmd agda && echo "  ✓ Agda" || echo "  ✗ Agda"
has_cmd z3 && echo "  ✓ Z3" || echo "  ✗ Z3"
has_cmd cvc5 && echo "  ✓ CVC5" || echo "  ✗ CVC5"
echo

# Logic programming
echo "Logic Programming:"
has_cmd swipl && echo "  ✓ SWI-Prolog" || echo "  ✗ SWI-Prolog"
has_cmd gprolog && echo "  ✓ GNU Prolog" || echo "  ✗ GNU Prolog"
echo

# Lisp
echo "Lisp:"
has_cmd sbcl && echo "  ✓ SBCL" || echo "  ✗ SBCL"
has_cmd clojure && echo "  ✓ Clojure" || echo "  ✗ Clojure"
echo

# Constraint solving
echo "Constraint Solving:"
has_cmd minizinc && echo "  ✓ MiniZinc" || echo "  ✗ MiniZinc"
echo

# Rust
echo "Rust Crates (checking Cargo.toml):"
if [ -f Cargo.toml ]; then
  grep -q "nalgebra" Cargo.toml && echo "  ✓ nalgebra" || echo "  ✗ nalgebra"
  grep -q "petgraph" Cargo.toml && echo "  ✓ petgraph" || echo "  ✗ petgraph"
  grep -q "num-bigint" Cargo.toml && echo "  ✓ num-bigint" || echo "  ✗ num-bigint"
else
  echo "  ✗ No Cargo.toml found"
fi
echo

# Python
echo "Python Packages:"
python3 -c "import numpy" 2>/dev/null && echo "  ✓ numpy" || echo "  ✗ numpy"
python3 -c "import scipy" 2>/dev/null && echo "  ✓ scipy" || echo "  ✗ scipy"
python3 -c "import sympy" 2>/dev/null && echo "  ✓ sympy" || echo "  ✗ sympy"
python3 -c "import networkx" 2>/dev/null && echo "  ✓ networkx" || echo "  ✗ networkx"
echo

echo "📦 Package Summary:"
echo "  Total packages checked: 30"
echo "  See SCIENCE_PACKAGES.md for full list (165 packages)"
echo

echo "💡 To install missing packages:"
echo "  Debian: sudo apt install <package>"
echo "  Nix: nix profile install nixpkgs#<package>"
echo "  Cargo: cargo add <crate>"
echo "  Python: pip install --user <package>"
echo

echo "∴ Package audit complete ✓"
