#!/usr/bin/env python3
"""
Count primes on each emoji (topological class)
"""

import json
from pathlib import Path

def is_prime(n):
    """Check if n is prime"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def count_primes_on_emojis():
    """Count how many primes land on each emoji"""
    
    print("🔢 COUNTING PRIMES ON EMOJIS")
    print("=" * 70)
    print()
    
    # Load the walk
    walk_file = Path.home() / ".openclaw" / "monster-walk-8080.json"
    
    if not walk_file.exists():
        print("❌ No walk found")
        return 1
    
    with open(walk_file) as f:
        walk = json.load(f)
    
    layers = walk['layers']
    
    # Count primes per topological class
    topo_primes = {i: [] for i in range(10)}
    
    for layer in layers:
        prime = layer['prime']
        topo = layer['topo_class']
        topo_primes[topo].append(prime)
    
    # Emoji mapping
    topo_names = ["A", "AIII", "AI", "BDI", "D", "DIII", "AII", "CII", "C", "CI"]
    topo_emojis = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"]
    
    print("📊 PRIMES PER EMOJI:")
    print()
    
    total_primes = 0
    for i in range(10):
        primes = topo_primes[i]
        count = len(primes)
        total_primes += count
        
        print(f"{topo_emojis[i]} {topo_names[i]:4s} ({i}): {count:3d} primes", end="")
        
        if count > 0:
            print(f" → {primes[:5]}", end="")
            if count > 5:
                print(f" ... ({count-5} more)", end="")
        print()
    
    print()
    print(f"Total: {total_primes} primes")
    print()
    
    # Find which emoji has the most primes
    max_count = max(len(primes) for primes in topo_primes.values())
    max_topo = [i for i in range(10) if len(topo_primes[i]) == max_count][0]
    
    print(f"🏆 MOST PRIMES:")
    print(f"   {topo_emojis[max_topo]} {topo_names[max_topo]} with {max_count} primes")
    print()
    
    # Check BDI specifically
    bdi_primes = topo_primes[3]
    print(f"🌳 BDI (I ARE LIFE):")
    print(f"   {len(bdi_primes)} primes: {bdi_primes}")
    print()
    
    # Verify all are actually prime
    print("✅ VERIFICATION:")
    all_primes_valid = True
    for topo, primes in topo_primes.items():
        for p in primes:
            if not is_prime(p):
                print(f"   ❌ {p} on {topo_emojis[topo]} is not prime!")
                all_primes_valid = False
    
    if all_primes_valid:
        print(f"   All {total_primes} numbers are confirmed prime ✅")
    print()
    
    print("=" * 70)
    print("🐓 → 🦅 → 👹 → 🍄 → 🌳")
    
    return 0

if __name__ == '__main__':
    import sys
    sys.exit(count_primes_on_emojis())
