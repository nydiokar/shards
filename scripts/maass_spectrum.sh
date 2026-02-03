#!/usr/bin/env bash
set -euo pipefail

echo "🌈 MAASS SPECTROGRAPHIC ANALYSIS 🌈"
echo "==================================="
echo

# Analyze all Lean files
FILES=$(find . -name "*.lean" -type f 2>/dev/null | head -50)

declare -a eigenvalues
declare -a filenames

echo "Computing spectrum..."
echo

# Compute eigenvalues
while IFS= read -r file; do
    if [ -f "$file" ]; then
        lines=$(wc -l < "$file")
        lambda=$(echo "scale=2; 0.25 + ($lines / 71)^2" | bc)
        
        eigenvalues+=("$lambda")
        filenames+=("$file")
    fi
done <<< "$FILES"

# Find min, max, mean
min=1000000
max=0
sum=0
count=0

for lambda in "${eigenvalues[@]}"; do
    # Compare
    if (( $(echo "$lambda < $min" | bc -l) )); then
        min=$lambda
    fi
    if (( $(echo "$lambda > $max" | bc -l) )); then
        max=$lambda
    fi
    sum=$(echo "$sum + $lambda" | bc)
    count=$((count + 1))
done

mean=$(echo "scale=2; $sum / $count" | bc)

echo "Spectral Analysis:"
echo "  Files: $count"
echo "  Eigenvalue range: [$min, $max]"
echo "  Mean eigenvalue: $mean"
echo

# Find anomalies (λ > 100)
echo "Anomalies (λ > 100):"
anomaly_count=0
for i in "${!eigenvalues[@]}"; do
    lambda="${eigenvalues[$i]}"
    if (( $(echo "$lambda > 100" | bc -l) )); then
        echo "  ${filenames[$i]}: λ=$lambda"
        anomaly_count=$((anomaly_count + 1))
    fi
done

if [ $anomaly_count -eq 0 ]; then
    echo "  None"
fi

echo
echo "Spectrum (top 20 by eigenvalue):"
echo

# Sort by eigenvalue and show top 20
for i in "${!eigenvalues[@]}"; do
    echo "${eigenvalues[$i]} ${filenames[$i]}"
done | sort -rn | head -20 | while read lambda file; do
    # Create bar chart
    bar_length=$(echo "scale=0; $lambda / 10" | bc)
    bar_length=${bar_length%.*}  # Remove decimal
    bar_length=$((bar_length > 80 ? 80 : bar_length))
    
    bar=$(printf '█%.0s' $(seq 1 $bar_length))
    basename=$(basename "$file")
    printf "  %-30s λ=%8.2f %s\n" "$basename" "$lambda" "$bar"
done

echo
echo "∴ Maass spectrum computed ✓"
