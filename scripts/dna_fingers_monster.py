#!/usr/bin/env python3
"""Map DNA, anatomy, fingers, and children's games to Monster symmetries"""

from dataclasses import dataclass
from typing import List, Dict

SHARDS = 71
DNA_BASES = ['A', 'T', 'G', 'C']  # 4 bases
FINGERS = 10  # 10 fingers (matches 10-fold way!)
HANDS = 2  # Left/Right (binary symmetry)

@dataclass
class DNAMapping:
    """DNA base to Monster shard"""
    base: str
    shard: int
    j_invariant: int
    az_class: str

@dataclass
class FingerMapping:
    """Finger to Monster coordinate"""
    finger: int  # 0-9
    hand: str    # 'L' or 'R'
    shard: int
    az_class: str
    bott_period: int

@dataclass
class FingerGame:
    """Children's finger game mapped to Monster"""
    name: str
    pattern: List[int]  # Finger sequence
    shard_path: List[int]
    symmetry: str

# DNA bases → Monster shards
DNA_TO_MONSTER = [
    DNAMapping('A', 2, 744 + 196884 * 2, 'A'),      # Adenine → Shard 2 (Unitary)
    DNAMapping('T', 3, 744 + 196884 * 3, 'AIII'),   # Thymine → Shard 3 (Chiral)
    DNAMapping('G', 5, 744 + 196884 * 5, 'AI'),     # Guanine → Shard 5 (Orthogonal)
    DNAMapping('C', 7, 744 + 196884 * 7, 'BDI'),    # Cytosine → Shard 7 (Chiral Orth)
]

# 10 fingers → 10-fold way (perfect match!)
FINGER_TO_TENFOLD = [
    FingerMapping(0, 'L', 2, 'A', 0),       # Left thumb
    FingerMapping(1, 'L', 3, 'AIII', 1),    # Left index
    FingerMapping(2, 'L', 5, 'AI', 2),      # Left middle
    FingerMapping(3, 'L', 7, 'BDI', 3),     # Left ring
    FingerMapping(4, 'L', 11, 'D', 4),      # Left pinky
    FingerMapping(5, 'R', 13, 'DIII', 5),   # Right thumb
    FingerMapping(6, 'R', 17, 'AII', 6),    # Right index
    FingerMapping(7, 'R', 19, 'CII', 7),    # Right middle
    FingerMapping(8, 'R', 23, 'C', 0),      # Right ring
    FingerMapping(9, 'R', 29, 'CI', 1),     # Right pinky
]

# Children's finger games
FINGER_GAMES = [
    FingerGame(
        "This Little Piggy",
        [0, 1, 2, 3, 4],  # Left hand sequence
        [2, 3, 5, 7, 11],
        "Left hand walk (A→AIII→AI→BDI→D)"
    ),
    FingerGame(
        "Itsy Bitsy Spider",
        [0, 5, 1, 6, 2, 7],  # Alternating thumbs and fingers
        [2, 13, 3, 17, 5, 19],
        "Hand alternation (L/R symmetry)"
    ),
    FingerGame(
        "Five Little Monkeys",
        [4, 3, 2, 1, 0],  # Countdown
        [11, 7, 5, 3, 2],
        "Reverse walk (D→BDI→AI→AIII→A)"
    ),
    FingerGame(
        "Pat-a-Cake",
        [0, 5, 0, 5],  # Clapping (both thumbs)
        [2, 13, 2, 13],
        "Binary oscillation (A↔DIII)"
    ),
]

def dna_sequence_to_monster(sequence: str) -> List[int]:
    """Map DNA sequence to Monster shard path"""
    base_map = {d.base: d.shard for d in DNA_TO_MONSTER}
    return [base_map.get(base, 0) for base in sequence.upper()]

def finger_pattern_to_shards(pattern: List[int]) -> List[int]:
    """Map finger pattern to Monster shards"""
    return [FINGER_TO_TENFOLD[f].shard for f in pattern if f < 10]

def analyze_finger_game(game: FingerGame) -> Dict:
    """Analyze Monster symmetry in finger game"""
    shards = finger_pattern_to_shards(game.pattern)
    
    # Compute symmetry properties
    is_symmetric = shards == shards[::-1]
    is_alternating = all(shards[i] != shards[i+1] for i in range(len(shards)-1))
    
    return {
        'name': game.name,
        'pattern': game.pattern,
        'shards': shards,
        'j_invariants': [744 + 196884 * s for s in shards],
        'symmetric': is_symmetric,
        'alternating': is_alternating,
        'symmetry_type': game.symmetry
    }

def main():
    print("DNA, Anatomy, Fingers → Monster Symmetries")
    print("=" * 60)
    print()
    
    # DNA mapping
    print("DNA Bases → Monster Shards:")
    for dna in DNA_TO_MONSTER:
        print(f"  {dna.base}: Shard {dna.shard:2d}, j = {dna.j_invariant:,}, AZ = {dna.az_class}")
    
    # Example DNA sequence
    print("\nExample DNA sequence: ATGC")
    dna_path = dna_sequence_to_monster("ATGC")
    print(f"  Monster path: {dna_path}")
    print(f"  AZ classes: {[d.az_class for d in DNA_TO_MONSTER]}")
    
    # Finger mapping
    print("\n10 Fingers → 10-Fold Way:")
    print(f"{'Finger':<15} {'Hand':<5} {'Shard':<6} {'AZ':<6} {'Bott':<5}")
    print("-" * 60)
    for f in FINGER_TO_TENFOLD:
        hand_name = "Left" if f.hand == 'L' else "Right"
        finger_names = ["Thumb", "Index", "Middle", "Ring", "Pinky"]
        name = f"{hand_name} {finger_names[f.finger % 5]}"
        print(f"{name:<15} {f.hand:<5} {f.shard:<6} {f.az_class:<6} {f.bott_period:<5}")
    
    # Finger games
    print("\nChildren's Finger Games → Monster Symmetries:")
    for game in FINGER_GAMES:
        analysis = analyze_finger_game(game)
        print(f"\n  {analysis['name']}:")
        print(f"    Pattern: {analysis['pattern']}")
        print(f"    Shards: {analysis['shards']}")
        print(f"    Symmetric: {analysis['symmetric']}")
        print(f"    Alternating: {analysis['alternating']}")
        print(f"    Type: {analysis['symmetry_type']}")
    
    # The key insight
    print("\n" + "=" * 60)
    print("KEY INSIGHT:")
    print("  10 fingers = 10-fold way (Altland-Zirnbauer)")
    print("  4 DNA bases = 4 fundamental symmetries (A, AIII, AI, BDI)")
    print("  2 hands = Binary symmetry (Left/Right, 0/1)")
    print("  Children's games = Monster group operations!")
    print("=" * 60)
    
    # Save mapping
    import json
    output = {
        'dna_mapping': [
            {'base': d.base, 'shard': d.shard, 'j_invariant': d.j_invariant, 'az_class': d.az_class}
            for d in DNA_TO_MONSTER
        ],
        'finger_mapping': [
            {'finger': f.finger, 'hand': f.hand, 'shard': f.shard, 'az_class': f.az_class, 'bott': f.bott_period}
            for f in FINGER_TO_TENFOLD
        ],
        'finger_games': [analyze_finger_game(g) for g in FINGER_GAMES],
        'insight': '10 fingers = 10-fold way, perfect match!'
    }
    
    with open('data/dna_fingers_monster.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\nMapping saved to: data/dna_fingers_monster.json")

if __name__ == '__main__':
    main()
