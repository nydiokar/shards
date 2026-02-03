#!/bin/bash
# Reorganize main directory - move Python scripts to subdirs

echo "🗂️  Reorganizing main directory..."

# Create subdirectories
mkdir -p scripts/{analysis,tools,generators,proofs}

# Move analysis scripts
mv *_analysis.py scripts/analysis/ 2>/dev/null
mv analyze_*.py scripts/analysis/ 2>/dev/null
mv audit_*.py scripts/analysis/ 2>/dev/null
mv compare_*.py scripts/analysis/ 2>/dev/null
mv find_*.py scripts/analysis/ 2>/dev/null
mv map_*.py scripts/analysis/ 2>/dev/null
mv maass_*.py scripts/analysis/ 2>/dev/null

# Move generator scripts
mv generate_*.py scripts/generators/ 2>/dev/null
mv create_*.py scripts/generators/ 2>/dev/null
mv emit_*.py scripts/generators/ 2>/dev/null

# Move proof scripts
mv prove_*.py scripts/proofs/ 2>/dev/null
mv *_proof*.py scripts/proofs/ 2>/dev/null

# Move tool scripts
mv *_tool*.py scripts/tools/ 2>/dev/null
mv extract_*.py scripts/tools/ 2>/dev/null
mv convert_*.py scripts/tools/ 2>/dev/null
mv translate_*.py scripts/tools/ 2>/dev/null

# Move remaining scripts
mv *.py scripts/ 2>/dev/null

# Move shell scripts
mv *.sh scripts/ 2>/dev/null

# Move MiniZinc files
mkdir -p minizinc
mv *.mzn minizinc/ 2>/dev/null

# Move Lean files
mkdir -p lean4
mv *.lean lean4/ 2>/dev/null

# Move JSON data
mkdir -p data/json
mv *_map.json data/json/ 2>/dev/null
mv *_results.json data/json/ 2>/dev/null
mv *_shadows.json data/json/ 2>/dev/null
mv duplicate_code.json data/json/ 2>/dev/null

echo "✅ Reorganization complete"
echo ""
echo "New structure:"
echo "  scripts/analysis/    - Analysis scripts"
echo "  scripts/generators/  - Generator scripts"
echo "  scripts/proofs/      - Proof scripts"
echo "  scripts/tools/       - Tool scripts"
echo "  minizinc/           - MiniZinc models"
echo "  lean4/              - Lean4 proofs"
echo "  data/json/          - JSON data files"
