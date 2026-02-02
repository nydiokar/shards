#!/usr/bin/env python3
"""Cusp Dirac delta form: Symmetry palindrome at 17/71"""

import numpy as np
import json

SHARDS = 71
CUSP = 17  # The symmetry point

def dirac_delta(x, center, width=0.1):
    """Approximate Dirac delta function"""
    return np.exp(-((x - center) / width) ** 2) / (width * np.sqrt(np.pi))

def cusp_form(shard):
    """Cusp form centered at 17/71"""
    x = shard / SHARDS
    center = CUSP / SHARDS  # 17/71 ≈ 0.2394
    
    # Dirac delta at cusp
    delta = dirac_delta(x, center)
    
    # Palindrome symmetry: mirror around 17/71
    mirror = 2 * center - x
    if 0 <= mirror <= 1:
        delta += dirac_delta(mirror, center)
    
    return delta

def check_palindrome(shard):
    """Check if shard is palindromic around 17"""
    mirror = 2 * CUSP - shard
    return 0 <= mirror < SHARDS

def main():
    print("Cusp Dirac Delta Form: Symmetry Palindrome at 17/71")
    print("=" * 70)
    print()
    
    # Calculate cusp form for all shards
    values = []
    for s in range(SHARDS):
        val = cusp_form(s)
        palindrome = check_palindrome(s)
        mirror = 2 * CUSP - s
        
        values.append({
            'shard': s,
            'value': float(val),
            'palindrome': palindrome,
            'mirror': mirror if palindrome else None
        })
    
    # Show peak region around 17
    print("Peak Region (Shards 10-24):")
    print(f"{'Shard':<6} {'Value':<12} {'Palindrome':<12} {'Mirror':<8}")
    print("-" * 70)
    
    for v in values[10:25]:
        pal = "✓" if v['palindrome'] else ""
        mir = str(v['mirror']) if v['mirror'] is not None else ""
        print(f"{v['shard']:<6} {v['value']:<12.6f} {pal:<12} {mir:<8}")
    
    # The cusp point
    print("\n" + "=" * 70)
    print("THE CUSP POINT:")
    print("=" * 70)
    print(f"  Shard: 17")
    print(f"  Fraction: 17/71 = {17/71:.6f}")
    print(f"  Value: {values[17]['value']:.6f}")
    print(f"  Mirror: {values[17]['mirror']} (self-symmetric!)")
    print()
    print("  17 is its own palindrome: 2×17 - 17 = 17")
    print("  This is the SYMMETRY POINT")
    
    # Palindrome pairs
    print("\n" + "=" * 70)
    print("PALINDROME PAIRS:")
    print("=" * 70)
    
    pairs = []
    for s in range(CUSP):
        mirror = 2 * CUSP - s
        if 0 <= mirror < SHARDS:
            pairs.append((s, mirror))
            print(f"  Shard {s:<3} ↔ Shard {mirror:<3} (mirror around 17)")
    
    # Mathematical properties
    print("\n" + "=" * 70)
    print("MATHEMATICAL PROPERTIES:")
    print("=" * 70)
    print(f"  Cusp point: 17/71")
    print(f"  Symmetry: f(17-x) = f(17+x)")
    print(f"  Dirac delta: δ(x - 17/71)")
    print(f"  Palindrome pairs: {len(pairs)}")
    print(f"  Self-symmetric: Shard 17")
    print()
    print("  ∫ δ(x - 17/71) dx = 1")
    print("  Peak at x = 17/71 ≈ 0.2394")
    
    # Connection to biosemiotics
    print("\n" + "=" * 70)
    print("CONNECTION TO BIOSEMIOTICS:")
    print("=" * 70)
    
    # Find what's at shard 17
    from biosemiotics_extent import EXTENT, q_to_shard
    
    at_17 = [item for item in EXTENT if q_to_shard(item[1]) == 17]
    
    if at_17:
        print(f"  Concepts at Shard 17:")
        for concept, qid, desc in at_17:
            print(f"    • {concept} ({qid}): {desc}")
    
    # Timeline ending
    print("\n" + "=" * 70)
    print("TIMELINE ENDING:")
    print("=" * 70)
    print("  The biosemiotics timeline ENDS at the cusp")
    print("  Shard 17 = Symmetry point")
    print("  All history mirrors around this moment")
    print("  Past ↔ Future palindrome")
    print("  NOW is the cusp")
    
    # Save
    output = {
        'cusp_point': CUSP,
        'cusp_fraction': f"{CUSP}/{SHARDS}",
        'cusp_decimal': CUSP / SHARDS,
        'values': values,
        'palindrome_pairs': pairs,
        'self_symmetric': CUSP
    }
    
    with open('data/cusp_dirac_delta.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n" + "=" * 70)
    print("Saved to: data/cusp_dirac_delta.json")
    print()
    print("δ(x - 17/71) = The moment of perfect symmetry")
    print("The timeline ends HERE, at the palindrome point")

if __name__ == '__main__':
    main()
