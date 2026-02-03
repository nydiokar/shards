#!/usr/bin/env python3
"""Fortnite emotes: Where they land and how they slap"""

import hashlib

SHARDS = 71
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
MUSES = ["Calliope","Clio","Erato","Euterpe","Melpomene","Polyhymnia","Terpsichore","Thalia","Urania"]

def j(s): return 744 + 196884 * s

def emote_shard(name):
    h = hashlib.sha256(name.encode()).digest()
    return int.from_bytes(h[:8], 'big') % SHARDS

def slap_power(shard):
    """How hard does this emote slap?"""
    power = 10
    if shard in PRIMES: power += 50  # Prime = HARD slap
    if shard % 9 == 6: power += 30   # Terpsichore (Dance Muse) = extra slap
    if shard % 10 == 0: power += 20  # 10-fold = slap
    return power

# Famous Fortnite emotes
FORTNITE = [
    "Floss", "Take the L", "Orange Justice", "Hype", "Best Mates",
    "Electro Shuffle", "Fresh", "Wiggle", "Boogie Down", "Intensity",
    "Scenario", "Rambunctious", "Infectious", "Smooth Moves", "Zany",
    "Llama Bell", "Freestylin'", "Breakin'", "Crackdown", "Groove Jam",
    "Tidy", "Jubilation", "Dab", "Disco Fever", "Boneless",
    "Squat Kick", "Chicken", "Reanimated", "Electro Swing", "Phone It In"
]

print("Fortnite Emotes: Where They Land & How They Slap")
print("=" * 70)
print()

results = []
for emote in FORTNITE:
    shard = emote_shard(emote)
    muse = MUSES[shard % 9]
    prime = shard in PRIMES
    slap = slap_power(shard)
    results.append((emote, shard, muse, prime, slap, j(shard)))

# Sort by slap power
results.sort(key=lambda x: x[4], reverse=True)

print(f"{'Emote':<20} {'Shard':<6} {'Muse':<12} {'Prime':<6} {'Slap':<6} {'j-inv':<10}")
print("-" * 70)

for emote, shard, muse, prime, slap, ji in results:
    p = "⭐" if prime else "  "
    print(f"{emote:<20} {shard:<6} {muse:<12} {p:<6} {slap:<6} {ji:<10}")

# Top slappers
print("\n" + "=" * 70)
print("🔥 TOP SLAPPERS:")
print("=" * 70)
for i, (emote, shard, muse, prime, slap, ji) in enumerate(results[:5], 1):
    print(f"{i}. {emote} - Shard {shard} ({muse}) - SLAPS {slap}/100")

# Muse distribution
print("\n" + "=" * 70)
print("MUSE DISTRIBUTION:")
print("=" * 70)
from collections import Counter
muse_counts = Counter(r[2] for r in results)
for muse, count in muse_counts.most_common():
    emotes = [r[0] for r in results if r[2] == muse][:3]
    print(f"{muse:<12}: {count} emotes - {', '.join(emotes)}")

print("\n💥 Prime shards slap hardest!")
print("🎭 Terpsichore (Dance Muse) adds extra slap!")
