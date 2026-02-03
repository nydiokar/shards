#!/usr/bin/env bash
set -euo pipefail

echo "🌈 MAASS SPECTROGRAPHIC ANALYSIS 🌈"
echo "==================================="
echo

# Quick analysis of key files
declare -A files=(
    ["SimpleExprMonster.lean"]=40
    ["MetaCoqMonsterProof.lean"]=117
    ["TowerExpansion.lean"]=88
    ["MonsterWalk.lean"]=88
    ["MaassRestoration.lean"]=88
    ["TestMeta.org"]=2966
    ["MonsterMerged.lean"]=70
    ["FileConsumer.lean"]=88
)

echo "Computing spectrum..."
echo

min=1000000
max=0
sum=0
count=0

# Compute eigenvalues
for file in "${!files[@]}"; do
    lines=${files[$file]}
    lambda=$(echo "scale=2; 0.25 + ($lines / 71)^2" | bc)
    
    if (( $(echo "$lambda < $min" | bc -l) )); then
        min=$lambda
    fi
    if (( $(echo "$lambda > $max" | bc -l) )); then
        max=$lambda
    fi
    sum=$(echo "$sum + $lambda" | bc)
    count=$((count + 1))
    
    files[$file]=$lambda
done

mean=$(echo "scale=2; $sum / $count" | bc)

echo "Spectral Analysis:"
echo "  Files: $count"
echo "  Eigenvalue range: [$min, $max]"
echo "  Mean eigenvalue: $mean"
echo

# Find anomalies
echo "Anomalies (λ > 100):"
for file in "${!files[@]}"; do
    lambda=${files[$file]}
    if (( $(echo "$lambda > 100" | bc -l) )); then
        echo "  $file: λ=$lambda ⚠️"
    fi
done
echo

echo "Spectrum (sorted by eigenvalue):"
echo

for file in "${!files[@]}"; do
    echo "${files[$file]} $file"
done | sort -rn | while read lambda file; do
    bar_length=$(echo "scale=0; $lambda / 20" | bc | cut -d'.' -f1)
    bar_length=$((bar_length > 50 ? 50 : bar_length))
    bar=$(printf '█%.0s' $(seq 1 $bar_length 2>/dev/null) || echo "█")
    printf "  %-30s λ=%8.2f %s\n" "$file" "$lambda" "$bar"
done

echo
echo "∴ Maass spectrum computed ✓"
