#!/usr/bin/env bash
set -euo pipefail

echo "🌈 MAASS SPECTROGRAM: Visual Frequency Analysis 🌈"
echo "=================================================="
echo

# Spectral data
declare -A spectrum=(
    ["SimpleExprMonster.lean"]="0.56"
    ["MonsterMerged.lean"]="1.21"
    ["TowerExpansion.lean"]="1.76"
    ["MonsterWalk.lean"]="1.76"
    ["MaassRestoration.lean"]="1.76"
    ["FileConsumer.lean"]="1.76"
    ["MetaCoqMonsterProof.lean"]="2.93"
    ["TestMeta.org"]="1744.98"
)

# Create spectrogram (frequency vs intensity)
echo "Spectrogram (20 frequency bands):"
echo

max=1744.98

for band in {19..0}; do
    threshold=$(echo "scale=2; $max * $band / 20" | bc)
    printf "%8.2f |" "$threshold"
    
    for file in "${!spectrum[@]}"; do
        lambda=${spectrum[$file]}
        if (( $(echo "$lambda >= $threshold" | bc -l) )); then
            echo -n "█"
        else
            echo -n " "
        fi
    done
    echo "|"
done

echo "         +"
echo "         Files: S M T M M F M T"
echo "                i e o o a i e e"
echo "                m r w n a l s s"
echo "                p g e s s e t t"
echo "                l e r t s C M M"
echo "                e d   e   o e e"
echo "                      r   n t t"
echo "                          s a a"
echo "                          u   ."
echo "                          m   o"
echo "                          e   r"
echo "                          r   g"
echo

echo "Legend:"
echo "  █ = Eigenvalue present at this frequency"
echo "  Vertical axis: Eigenvalue (λ)"
echo "  Horizontal axis: Files"
echo

echo "Key observations:"
echo "  - TestMeta.org dominates spectrum (λ=1744.98)"
echo "  - Most files cluster at λ~1.76 (88 lines)"
echo "  - SimpleExprMonster lowest (λ=0.56, 40 lines)"
echo "  - Clear spectral gap between normal files and anomaly"
echo

echo "∴ Maass spectrogram complete ✓"
