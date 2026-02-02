#!/usr/bin/env python3
"""Monster Walk through LMFDB Magic Numbers"""
import json
from pathlib import Path

# Magic numbers from LMFDB
MAGIC_NUMBERS = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 59, 71,  # Primes
    12, 24, 31, 72,  # Connections
    240, 264, 480, 504, 691, 744, 1728,  # Eisenstein, tau, j-invariant
    196883, 196884, 21493760  # Monster, moonshine
]

TOPO_EMOJI = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"]
TOPO_NAMES = ["A", "AIII", "AI", "BDI", "D", "DIII", "AII", "CII", "C", "CI"]

def to_topo_class(n):
    """Map number to topological class (mod 10)"""
    return n % 10

def to_bott_level(n):
    """Map to Bott periodicity (mod 8)"""
    return n % 8

def is_bdi(n):
    """Check if number is BDI (life-bearing)"""
    return n % 10 == 3

def prime_factorization(n):
    """Simple prime factorization"""
    if n < 2:
        return []
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def monster_walk(numbers):
    """Walk through numbers in Monster space"""
    walk = []
    
    for i, n in enumerate(numbers):
        topo = to_topo_class(n)
        bott = to_bott_level(n)
        factors = prime_factorization(n)
        
        step = {
            'layer': i,
            'number': n,
            'topo_class': topo,
            'topo_name': TOPO_NAMES[topo],
            'emoji': TOPO_EMOJI[topo],
            'bott_level': bott,
            'is_bdi': is_bdi(n),
            'is_prime': len(factors) == 1 and factors[0] == n,
            'factors': factors,
            'frequency': n * 10  # Hz
        }
        
        walk.append(step)
    
    return walk

def analyze_walk(walk):
    """Analyze Monster Walk patterns"""
    stats = {
        'total_steps': len(walk),
        'bdi_count': sum(1 for s in walk if s['is_bdi']),
        'prime_count': sum(1 for s in walk if s['is_prime']),
        'topo_distribution': {},
        'bott_distribution': {},
        'bdi_layers': [s['layer'] for s in walk if s['is_bdi']],
        'rooster_layer': next((s['layer'] for s in walk if s['number'] == 71), None),
        'monster_layer': next((s['layer'] for s in walk if s['number'] == 196884), None)
    }
    
    for step in walk:
        topo = step['topo_name']
        bott = step['bott_level']
        stats['topo_distribution'][topo] = stats['topo_distribution'].get(topo, 0) + 1
        stats['bott_distribution'][bott] = stats['bott_distribution'].get(bott, 0) + 1
    
    return stats

def main():
    print("🐓 Monster Walk through LMFDB Magic Numbers")
    print("=" * 80)
    
    # Sort numbers for walk
    numbers = sorted(set(MAGIC_NUMBERS))
    
    print(f"\nWalking through {len(numbers)} magic numbers...")
    
    # Perform walk
    walk = monster_walk(numbers)
    
    # Analyze
    stats = analyze_walk(walk)
    
    print(f"\n📊 WALK STATISTICS:")
    print(f"  Total steps: {stats['total_steps']}")
    print(f"  BDI (life-bearing): {stats['bdi_count']}")
    print(f"  Primes: {stats['prime_count']}")
    print(f"  Rooster (71) at layer: {stats['rooster_layer']}")
    print(f"  Monster (196884) at layer: {stats['monster_layer']}")
    
    print(f"\n🌊 TOPOLOGICAL DISTRIBUTION:")
    for topo, count in sorted(stats['topo_distribution'].items()):
        emoji_idx = TOPO_NAMES.index(topo)
        print(f"  {TOPO_EMOJI[emoji_idx]} {topo}: {count}")
    
    print(f"\n🔮 BOTT PERIODICITY:")
    for bott, count in sorted(stats['bott_distribution'].items()):
        print(f"  Level {bott}: {count}")
    
    print(f"\n🌳 BDI LAYERS (life-bearing):")
    bdi_steps = [walk[i] for i in stats['bdi_layers']]
    for step in bdi_steps:
        print(f"  Layer {step['layer']:2d}: {step['number']:8d} {step['emoji']} {step['topo_name']}")
    
    print(f"\n📍 KEY WAYPOINTS:")
    for step in walk:
        if step['number'] in [3, 13, 23, 71, 196884]:
            factors_str = '×'.join(map(str, step['factors']))
            print(f"  Layer {step['layer']:2d}: {step['number']:8d} {step['emoji']} {step['topo_name']} = {factors_str}")
    
    print(f"\n🎯 THE WALK PATH:")
    for i, step in enumerate(walk[:20]):  # First 20 steps
        arrow = " → " if i < 19 else ""
        print(f"{step['emoji']}{arrow}", end="")
    if len(walk) > 20:
        print(f"... ({len(walk)-20} more)")
    else:
        print()
    
    # Save walk
    output = {
        'walk': walk,
        'stats': stats,
        'numbers': numbers
    }
    
    output_file = Path.home() / 'introspector' / 'monster_walk_lmfdb.json'
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n💾 Saved to {output_file}")
    
    # Create visualization data
    viz_file = Path.home() / 'introspector' / 'docs' / 'monster_walk_data.js'
    with open(viz_file, 'w') as f:
        f.write(f"const MONSTER_WALK = {json.dumps(walk, indent=2)};\n")
        f.write(f"const WALK_STATS = {json.dumps(stats, indent=2)};\n")
    
    print(f"📊 Visualization data: {viz_file}")

if __name__ == '__main__':
    main()
