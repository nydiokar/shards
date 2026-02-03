#!/usr/bin/env python3
"""Load 9 Muses into Monster shards, deduplicate, prepare for MiniZinc"""

import hashlib
import json

SHARDS = 71
MUSES = [
    {"name": "Calliope", "domain": "Epic Poetry", "layer": 0, "emoji": "🎭", "prime": 2},
    {"name": "Clio", "domain": "History", "layer": 8, "emoji": "📜", "prime": 3},
    {"name": "Erato", "domain": "Love Poetry", "layer": 16, "emoji": "💖", "prime": 5},
    {"name": "Euterpe", "domain": "Music", "layer": 24, "emoji": "🎵", "prime": 7},
    {"name": "Melpomene", "domain": "Tragedy", "layer": 32, "emoji": "😢", "prime": 11},
    {"name": "Polyhymnia", "domain": "Hymns", "layer": 40, "emoji": "🙏", "prime": 13},
    {"name": "Terpsichore", "domain": "Dance", "layer": 48, "emoji": "💃", "prime": 17},
    {"name": "Thalia", "domain": "Comedy", "layer": 56, "emoji": "😂", "prime": 19},
    {"name": "Urania", "domain": "Astronomy", "layer": 64, "emoji": "✨", "prime": 23},
]

def muse_to_shard(muse):
    """Map muse to Monster shard"""
    h = hashlib.sha256(muse['name'].encode()).digest()
    return int.from_bytes(h[:8], 'big') % SHARDS

def load_emojis(filepath):
    """Load and deduplicate emojis"""
    emojis = set()
    try:
        with open(filepath) as f:
            for line in f:
                line = line.strip()
                # Extract emoji characters
                for char in line:
                    if ord(char) > 0x1F000:  # Emoji range
                        emojis.add(char)
    except:
        pass
    return list(emojis)

# Map muses to shards
for muse in MUSES:
    muse['shard'] = muse_to_shard(muse)
    muse['j_invariant'] = 744 + 196884 * muse['shard']

print("9 Muses → Monster Shards")
print("=" * 70)
print(f"{'Muse':<15} {'Domain':<15} {'Layer':<7} {'Shard':<6} {'Prime':<6} {'Emoji':<5}")
print("-" * 70)

for m in MUSES:
    print(f"{m['name']:<15} {m['domain']:<15} {m['layer']:<7} {m['shard']:<6} {m['prime']:<6} {m['emoji']:<5}")

# Load emojis
print("\nLoading emojis...")
emojis = load_emojis('data/.locate-emojis-26-2-2-940.txt')
print(f"✓ {len(emojis)} unique emojis")

# Shard emojis
emoji_shards = {}
for emoji in emojis[:1000]:  # First 1000
    h = hashlib.sha256(emoji.encode()).digest()
    shard = int.from_bytes(h[:8], 'big') % SHARDS
    if shard not in emoji_shards:
        emoji_shards[shard] = []
    emoji_shards[shard].append(emoji)

print(f"✓ Distributed across {len(emoji_shards)} shards")

# Generate MiniZinc data
print("\nGenerating MiniZinc data...")

mzn_data = {
    'n_muses': len(MUSES),
    'n_shards': SHARDS,
    'muse_shards': [m['shard'] for m in MUSES],
    'muse_primes': [m['prime'] for m in MUSES],
    'muse_layers': [m['layer'] for m in MUSES],
    'emojis_per_shard': {s: len(e) for s, e in emoji_shards.items()}
}

with open('data/muses_shards.dzn', 'w') as f:
    f.write(f"n_muses = {mzn_data['n_muses']};\n")
    f.write(f"n_shards = {mzn_data['n_shards']};\n")
    f.write(f"muse_shards = {mzn_data['muse_shards']};\n")
    f.write(f"muse_primes = {mzn_data['muse_primes']};\n")
    f.write(f"muse_layers = {mzn_data['muse_layers']};\n")

print("✓ Saved to data/muses_shards.dzn")

# Save full data
output = {
    'muses': MUSES,
    'emoji_count': len(emojis),
    'emoji_shards': {str(k): v[:10] for k, v in emoji_shards.items()},  # First 10 per shard
    'minizinc_data': mzn_data
}

with open('data/muses_emojis_shards.json', 'w') as f:
    json.dump(output, f, indent=2)

print("✓ Saved to data/muses_emojis_shards.json")
print()
print("Ready for MiniZinc optimization!")
