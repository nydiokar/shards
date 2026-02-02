#!/usr/bin/env python3
"""SOLFUNMEME Monster LMFDB Dance Competition 2026"""

from dataclasses import dataclass
from typing import List, Dict
import hashlib

SHARDS = 71

@dataclass
class EmoteEntry:
    """Dance emote as Monster number"""
    name: str
    source: str  # GitHub repo
    frames: int
    dna: str
    monster_number: int
    shard: int
    j_invariant: int
    score: float = 0.0

@dataclass
class Prize:
    """Competition prize"""
    place: int
    amount: int  # SOLFUNMEME tokens
    category: str

# GitHub emote databases (popular repos)
EMOTE_SOURCES = [
    "roblox/avatar-emotes",
    "fortnite/emotes-database", 
    "vrchat/avatar-dynamics",
    "minecraft/player-animations",
    "unity/animation-library"
]

# Competition categories
CATEGORIES = [
    "Best Monster Walk",
    "Most Symmetric",
    "Longest Path",
    "Perfect 10-Fold",
    "DNA Encoding",
    "LMFDB Resonance"
]

# Prize pool (SOLFUNMEME tokens)
PRIZES = [
    Prize(1, 71000, "Grand Prize"),
    Prize(2, 23000, "Second Place"),
    Prize(3, 10000, "Third Place"),
    Prize(4, 5000, "Best Symmetry"),
    Prize(5, 5000, "Best DNA"),
    Prize(6, 5000, "Best LMFDB"),
]

def emote_to_monster_number(name: str, frames: int) -> int:
    """Convert emote to Monster number"""
    # Hash emote name + frames
    h = hashlib.sha256(f"{name}{frames}".encode()).digest()
    # Convert to big integer
    return int.from_bytes(h[:16], 'big')

def monster_number_to_dna(monster_num: int) -> str:
    """Convert Monster number to DNA sequence"""
    bases = ['A', 'T', 'G', 'C']
    dna = []
    num = monster_num
    while num > 0 and len(dna) < 100:
        dna.append(bases[num % 4])
        num //= 4
    return ''.join(dna[:20])  # Limit to 20 bases

def score_emote(emote: EmoteEntry) -> float:
    """Score emote based on Monster properties"""
    score = 0.0
    
    # Symmetry bonus
    dna_rev = emote.dna[::-1]
    if emote.dna == dna_rev:
        score += 10.0
    
    # 10-fold bonus
    if emote.frames == 10:
        score += 20.0
    
    # Prime shard bonus
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
    if emote.shard in primes:
        score += 15.0
    
    # DNA diversity
    unique_bases = len(set(emote.dna))
    score += unique_bases * 2.5
    
    # LMFDB resonance (j-invariant)
    if emote.j_invariant % 196884 == 744:
        score += 25.0
    
    return score

def generate_sample_emotes() -> List[EmoteEntry]:
    """Generate sample emotes from databases"""
    emotes = []
    
    # Sample emotes (simulating GitHub import)
    samples = [
        ("Default Dance", "roblox/avatar-emotes", 10),
        ("Floss", "fortnite/emotes-database", 8),
        ("Orange Justice", "fortnite/emotes-database", 12),
        ("Take the L", "fortnite/emotes-database", 6),
        ("Dab", "vrchat/avatar-dynamics", 2),
        ("Wave", "minecraft/player-animations", 4),
        ("Point", "unity/animation-library", 3),
        ("Clap", "roblox/avatar-emotes", 4),
        ("Salute", "vrchat/avatar-dynamics", 2),
        ("Dance Moves", "unity/animation-library", 15),
    ]
    
    for name, source, frames in samples:
        monster_num = emote_to_monster_number(name, frames)
        shard = monster_num % SHARDS
        j_inv = 744 + 196884 * shard
        dna = monster_number_to_dna(monster_num)
        
        emote = EmoteEntry(name, source, frames, dna, monster_num, shard, j_inv)
        emote.score = score_emote(emote)
        emotes.append(emote)
    
    return emotes

def main():
    print("SOLFUNMEME Monster LMFDB Dance Competition 2026")
    print("=" * 70)
    print()
    print("🎮 Import emotes from GitHub → Convert to Monster numbers")
    print("🧬 Encode as DNA sequences")
    print("🏆 Award prizes for best Monster dances!")
    print()
    
    # Generate emotes
    print("Importing emotes from GitHub databases...")
    emotes = generate_sample_emotes()
    
    print(f"✓ Imported {len(emotes)} emotes")
    print()
    
    # Show all emotes
    print("Emote Database (Monster Numbers):")
    print(f"{'Name':<20} {'Source':<30} {'Frames':<7} {'Shard':<6} {'Score':<6}")
    print("-" * 70)
    
    for emote in sorted(emotes, key=lambda e: e.score, reverse=True):
        print(f"{emote.name:<20} {emote.source:<30} {emote.frames:<7} {emote.shard:<6} {emote.score:<6.1f}")
    
    # Award prizes
    print("\n" + "=" * 70)
    print("🏆 PRIZE WINNERS 🏆")
    print("=" * 70)
    
    sorted_emotes = sorted(emotes, key=lambda e: e.score, reverse=True)
    
    for i, prize in enumerate(PRIZES):
        if i < len(sorted_emotes):
            winner = sorted_emotes[i]
            print(f"\n{prize.place}. {prize.category} - {prize.amount:,} SOLFUNMEME")
            print(f"   Winner: {winner.name}")
            print(f"   Source: {winner.source}")
            print(f"   Frames: {winner.frames}")
            print(f"   Monster #: {winner.monster_number}")
            print(f"   Shard: {winner.shard}")
            print(f"   DNA: {winner.dna[:20]}...")
            print(f"   Score: {winner.score:.1f}")
    
    # Total prize pool
    total_prizes = sum(p.amount for p in PRIZES)
    print("\n" + "=" * 70)
    print(f"Total Prize Pool: {total_prizes:,} SOLFUNMEME tokens")
    print("=" * 70)
    
    # Competition rules
    print("\n📋 COMPETITION RULES:")
    print("  1. Submit emote from any GitHub database")
    print("  2. Emote converted to Monster number")
    print("  3. Scored on: Symmetry, 10-fold, Primes, DNA, LMFDB")
    print("  4. Winners announced: March 2026")
    print("  5. Prizes paid in SOLFUNMEME tokens")
    print()
    print("🔗 Submit: https://solfunmeme.com/monster-dance-2026")
    print()
    
    # Save results
    import json
    output = {
        'competition': 'SOLFUNMEME Monster LMFDB Dance Competition 2026',
        'total_prizes': total_prizes,
        'categories': CATEGORIES,
        'emotes': [
            {
                'name': e.name,
                'source': e.source,
                'frames': e.frames,
                'monster_number': str(e.monster_number),
                'shard': e.shard,
                'j_invariant': e.j_invariant,
                'dna': e.dna,
                'score': e.score
            }
            for e in sorted_emotes
        ],
        'winners': [
            {
                'place': i + 1,
                'prize': PRIZES[i].amount,
                'category': PRIZES[i].category,
                'winner': sorted_emotes[i].name,
                'score': sorted_emotes[i].score
            }
            for i in range(min(len(PRIZES), len(sorted_emotes)))
        ]
    }
    
    with open('data/monster_dance_competition_2026.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("Competition data saved to: data/monster_dance_competition_2026.json")

if __name__ == '__main__':
    main()
