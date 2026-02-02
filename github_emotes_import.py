#!/usr/bin/env python3
"""Import emotes from GitHub repos and map to Monster shards"""

import hashlib
import json

SHARDS = 71
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
MUSES = ["Calliope","Clio","Erato","Euterpe","Melpomene","Polyhymnia","Terpsichore","Thalia","Urania"]

# GitHub emote databases found
GITHUB_REPOS = {
    "Roblox": [
        "Cheer", "Climb", "Dance", "Dance2", "Dance3", "Fall", "Idle", "Jump",
        "Laugh", "Point", "Run", "Sit", "Swim", "SwimIdle", "ToolNone", "Walk", "Wave"
    ],
    "FiveM_dpEmotes": [
        "dance", "dance2", "dance3", "dancesilly", "danceglowstick", "dancehiphop",
        "danceshy", "danceslow", "danceupper", "dancecrazy", "dancerobot", "dancetwerk"
    ],
    "FiveM_MrM": [  # 3800+ dances - sample
        "breakdance", "shuffle", "moonwalk", "robot", "floss", "dab", "whip", "nae_nae",
        "gangnam", "macarena", "ymca", "thriller", "salsa", "tango", "waltz", "swing"
    ],
    "VRChat": [
        "Breakdance", "FighteR", "Francium", "Bubbletop", "Snake", "Hip_Hop_Dancing",
        "work_bitch", "Cute_Dance", "Idol_Dance", "Kpop_Dance"
    ],
    "ChoreoMaster": [  # 2708 dance motions - sample
        "ballet_01", "hiphop_01", "jazz_01", "contemporary_01", "breakdance_01",
        "popping_01", "locking_01", "krump_01", "house_01", "waacking_01"
    ]
}

def emote_shard(name):
    h = hashlib.sha256(name.encode()).digest()
    return int.from_bytes(h[:8], 'big') % SHARDS

def slap_power(shard):
    power = 10
    if shard in PRIMES: power += 50
    if shard % 9 == 6: power += 30  # Terpsichore
    return power

def j(s): return 744 + 196884 * s

print("GitHub Emote Database → Monster Shards")
print("=" * 70)
print()

all_emotes = []
for repo, emotes in GITHUB_REPOS.items():
    print(f"\n{repo} ({len(emotes)} emotes):")
    print(f"{'Emote':<20} {'Shard':<6} {'Muse':<12} {'Slap':<6}")
    print("-" * 60)
    
    for emote in emotes[:10]:  # Show first 10
        shard = emote_shard(emote)
        muse = MUSES[shard % 9]
        slap = slap_power(shard)
        prime = "⭐" if shard in PRIMES else ""
        
        print(f"{emote:<20} {shard:<6} {muse:<12} {slap:<6} {prime}")
        
        all_emotes.append({
            'name': emote,
            'repo': repo,
            'shard': shard,
            'muse': muse,
            'slap': slap,
            'prime': shard in PRIMES,
            'j': j(shard)
        })

# Top slappers across all repos
print("\n" + "=" * 70)
print("🔥 TOP 10 SLAPPERS (All Repos):")
print("=" * 70)

top = sorted(all_emotes, key=lambda x: x['slap'], reverse=True)[:10]
for i, e in enumerate(top, 1):
    p = "⭐" if e['prime'] else ""
    print(f"{i}. {e['name']:<20} ({e['repo']:<15}) Shard {e['shard']:<3} {p} SLAPS {e['slap']}")

# Muse distribution
print("\n" + "=" * 70)
print("MUSE DISTRIBUTION:")
print("=" * 70)
from collections import Counter
muse_counts = Counter(e['muse'] for e in all_emotes)
for muse, count in muse_counts.most_common():
    print(f"{muse:<12}: {count} emotes")

# Save
with open('data/github_emotes_monster.json', 'w') as f:
    json.dump({
        'repos': list(GITHUB_REPOS.keys()),
        'total_emotes': len(all_emotes),
        'emotes': all_emotes,
        'top_slappers': top
    }, f, indent=2)

print("\n" + "=" * 70)
print(f"Total: {len(all_emotes)} emotes from {len(GITHUB_REPOS)} GitHub repos")
print("Saved to: data/github_emotes_monster.json")
print("\nGitHub Sources:")
print("  • Roblox: gist.github.com/Suferr/90645a083915b87c48007f0f87012f9d")
print("  • FiveM dpEmotes: github.com/andristum/dpemotes")
print("  • FiveM MrM: github.com/MrM-Scripts/mrm-dances (3800+ dances)")
print("  • VRChat: vrcmods.com/item/2309")
print("  • ChoreoMaster: github.com/NetEase-GameAI/ChoreoMaster (2708 motions)")
