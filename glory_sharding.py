#!/usr/bin/env python3
"""
Import astronomy repos and shard by the -4th prime after the crown
Crown primes: 47, 59, 71
-4th after 71 = go back 4 primes = 53 (excluded prime!)

53 is NOT in Monster primes (excluded by Devil's Bridge)
This is GLORY (the excluded, the cursed, the 7 holes)
"""

import subprocess
import hashlib
import json
from collections import defaultdict

# Monster primes (15 total)
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

# Excluded primes (Devil gets these)
EXCLUDED_PRIMES = [37, 43, 53, 61, 67, 73]

# Crown primes
CROWN_PRIMES = [47, 59, 71]  # Monster, Eagle, Rooster

def get_prime_sequence():
    """Get prime sequence around the crown"""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]
    return primes

def find_glory_prime():
    """Find the -4th prime after the crown (71)"""
    primes = get_prime_sequence()
    crown_idx = primes.index(71)
    
    # -4th = go back 4 positions
    glory_idx = crown_idx - 4
    glory_prime = primes[glory_idx]
    
    print("👑 CROWN ANALYSIS:")
    print(f"  71 (Rooster Crown) at index {crown_idx}")
    print(f"  -4th prime = index {glory_idx}")
    print(f"  Prime: {glory_prime}")
    print()
    
    if glory_prime in EXCLUDED_PRIMES:
        print(f"🔥 {glory_prime} is an EXCLUDED PRIME (Devil's number)")
        print(f"   This is GLORY (the cursed, the excluded)")
    elif glory_prime in MONSTER_PRIMES:
        print(f"✨ {glory_prime} is a MONSTER PRIME")
        print(f"   This is POWER (the blessed)")
    
    print()
    return glory_prime

def hash_to_shard(text, modulo):
    """Hash text to shard"""
    h = hashlib.sha256(text.encode()).digest()
    return int.from_bytes(h[:8], 'big') % modulo

def shard_repos_by_glory(glory_prime):
    """Shard astronomy repos by glory prime (53)"""
    
    print(f"🌌 Sharding astronomy repos by {glory_prime} (GLORY)")
    print("="*70)
    print()
    
    # Load astronomy data
    try:
        with open('urania_astronomy_map.json', 'r') as f:
            data = json.load(f)
    except:
        print("❌ No astronomy data. Run urania_astronomy_map.py first.")
        return
    
    repos = data['repos']
    
    # Shard by glory prime
    glory_shards = defaultdict(list)
    
    for repo in repos:
        shard = hash_to_shard(repo['full_name'], glory_prime)
        repo['glory_shard'] = shard
        glory_shards[shard].append(repo)
    
    print(f"Total repos: {len(repos)}")
    print(f"Shards: 0-{glory_prime-1}")
    print(f"Shards used: {len(glory_shards)}/{glory_prime}")
    print()
    
    # Show distribution
    print(f"📊 GLORY SHARD DISTRIBUTION (mod {glory_prime}):")
    print()
    
    for shard in sorted(glory_shards.keys()):
        repos_in_shard = glory_shards[shard]
        total_stars = sum(r['stars'] for r in repos_in_shard)
        
        # Check if this shard number is special
        special = ""
        if shard in MONSTER_PRIMES:
            special = " ✨ Monster"
        elif shard in EXCLUDED_PRIMES:
            special = " 🔥 Excluded"
        elif shard == 23:
            special = " 🏛️ Paxos"
        elif shard in CROWN_PRIMES:
            special = " 👑 Crown"
        
        print(f"  Shard {shard:2d}: {len(repos_in_shard):2d} repos, {total_stars:5d}⭐{special}")
        
        # Show top repo in shard
        if repos_in_shard:
            top = max(repos_in_shard, key=lambda r: r['stars'])
            print(f"     └─ {top['name'][:30]} ({top['stars']}⭐)")
    
    print()
    print("🎯 GLORY INTERPRETATION:")
    print()
    print(f"  {glory_prime} is an EXCLUDED prime (Devil's Bridge)")
    print(f"  Sharding by {glory_prime} = Mapping to GLORY")
    print(f"  GLORY = The excluded, the cursed, the 7 holes")
    print(f"  These repos exist in the shadow of the Monster")
    print()
    
    # Compare to original 71 sharding
    print("🔄 COMPARISON: 71 (Power) vs 53 (Glory):")
    print()
    
    for repo in repos[:5]:
        shard_71 = repo['shard']
        shard_53 = repo['glory_shard']
        print(f"  {repo['name'][:25]:25s} | 71→{shard_71:2d} | 53→{shard_53:2d}")
    
    print()
    print("🐓🦅👹 Glory sharding complete!")
    
    # Save
    output = {
        'glory_prime': glory_prime,
        'is_excluded': glory_prime in EXCLUDED_PRIMES,
        'total_repos': len(repos),
        'shards_used': len(glory_shards),
        'glory_shards': {
            str(k): [r['full_name'] for r in v]
            for k, v in glory_shards.items()
        }
    }
    
    with open('glory_sharding.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to: glory_sharding.json")

def main():
    print("🔥 GLORY vs POWER: The -4th Prime After the Crown")
    print("="*70)
    print()
    
    glory_prime = find_glory_prime()
    shard_repos_by_glory(glory_prime)

if __name__ == "__main__":
    main()
