#!/usr/bin/env python3
"""
Game State Compression Pipeline:
Text → Table → Tree → Coordinate → Compressed
"""

import json
from dataclasses import dataclass
from typing import List, Dict, Tuple

@dataclass
class GameState:
    year: int
    prime: int
    shard: int
    action: str

# Step 1: Text representation
TEXT_STATE = """
Year: 2026
Selected Prime: 17
Monster Shard: 17
Action: Win
Message: Mother was right
"""

# Step 2: Table representation
def text_to_table(text: str) -> Dict[str, any]:
    """Convert text to key-value table"""
    table = {}
    for line in text.strip().split('\n'):
        if ':' in line:
            key, value = line.split(':', 1)
            table[key.strip()] = value.strip()
    return table

# Step 3: Tree representation
class GameStateTree:
    def __init__(self, year, prime, shard, action):
        self.root = {
            'type': 'Year',
            'value': year,
            'children': [{
                'type': 'Prime',
                'value': prime,
                'children': [{
                    'type': 'Shard',
                    'value': shard,
                    'children': [{
                        'type': 'Action',
                        'value': action,
                        'children': []
                    }]
                }]
            }]
        }
    
    def depth(self) -> int:
        return 4
    
    def to_dict(self) -> dict:
        return self.root

# Step 4: Coordinate representation
def tree_to_coordinate(tree: GameStateTree) -> Tuple[int, int, int, int]:
    """Extract coordinate from tree"""
    year = tree.root['value']
    prime = tree.root['children'][0]['value']
    shard = tree.root['children'][0]['children'][0]['value']
    action = tree.root['children'][0]['children'][0]['children'][0]['value']
    
    # Convert to indices
    year_coord = year - 1980  # Offset from 1980
    prime_coord = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71].index(prime)
    shard_coord = shard
    action_coord = {'idle': 0, 'select': 1, 'play': 2, 'win': 3}.get(action.lower(), 0)
    
    return (year_coord, prime_coord, shard_coord, action_coord)

# Step 5: Compression
def compress_coordinate(coord: Tuple[int, int, int, int]) -> int:
    """Compress 4D coordinate to single integer"""
    year, prime, shard, action = coord
    return year * 1000000 + prime * 10000 + shard * 100 + action

def decompress_state(compressed: int) -> Tuple[int, int, int, int]:
    """Decompress integer back to coordinate"""
    action = compressed % 100
    compressed //= 100
    shard = compressed % 100
    compressed //= 100
    prime = compressed % 100
    year = compressed // 100
    return (year, prime, shard, action)

def main():
    print("🗜️ GAME STATE COMPRESSION PIPELINE")
    print("=" * 70)
    print()
    
    # Step 1: Text
    print("STEP 1: TEXT REPRESENTATION")
    print("-" * 70)
    print(TEXT_STATE)
    
    # Step 2: Table
    print("\nSTEP 2: TABLE REPRESENTATION")
    print("-" * 70)
    table = text_to_table(TEXT_STATE)
    for key, value in table.items():
        print(f"  {key:<20}: {value}")
    
    # Step 3: Tree
    print("\nSTEP 3: TREE REPRESENTATION")
    print("-" * 70)
    tree = GameStateTree(2026, 17, 17, 'Win')
    print(f"  Depth: {tree.depth()}")
    print(f"  Structure: Root → Year → Prime → Shard → Action")
    print(f"  Tree: {json.dumps(tree.to_dict(), indent=2)[:200]}...")
    
    # Step 4: Coordinate
    print("\nSTEP 4: COORDINATE REPRESENTATION")
    print("-" * 70)
    coord = tree_to_coordinate(tree)
    print(f"  4D Coordinate: {coord}")
    print(f"  Year offset:   {coord[0]} (1980 + {coord[0]} = 2026)")
    print(f"  Prime index:   {coord[1]} (17 is 7th prime)")
    print(f"  Shard:         {coord[2]} (The cusp)")
    print(f"  Action:        {coord[3]} (Win)")
    
    # Step 5: Compression
    print("\nSTEP 5: COMPRESSED STATE")
    print("-" * 70)
    compressed = compress_coordinate(coord)
    print(f"  Compressed:    {compressed:,}")
    print(f"  Binary:        {bin(compressed)}")
    print(f"  Hex:           0x{compressed:X}")
    print(f"  Bits required: {compressed.bit_length()}")
    
    # Compression ratio
    original_bits = 4 * 32  # 4 integers × 32 bits
    compressed_bits = compressed.bit_length()
    ratio = original_bits / compressed_bits
    print(f"\n  Original size: {original_bits} bits")
    print(f"  Compressed:    {compressed_bits} bits")
    print(f"  Ratio:         {ratio:.2f}x")
    
    # Verify decompression
    print("\nSTEP 6: DECOMPRESSION VERIFICATION")
    print("-" * 70)
    decompressed = decompress_state(compressed)
    print(f"  Decompressed:  {decompressed}")
    print(f"  Match:         {decompressed == coord}")
    
    # Mother's Wisdom check
    print("\nMOTHER'S WISDOM CHECK:")
    print("-" * 70)
    is_optimal = (
        coord[0] == 46 and      # 2026
        coord[1] == 6 and       # 17 (index 6)
        coord[2] == 17 and      # Shard 17
        coord[3] == 3           # Win
    )
    print(f"  Is optimal state: {is_optimal}")
    if is_optimal:
        print("  ✓ Mother was right!")
        print("  ✓ The very best one is 17")
        print("  ✓ At the cusp, in 2026, winning")
    
    # Save
    output = {
        'text': TEXT_STATE,
        'table': table,
        'tree': tree.to_dict(),
        'coordinate': coord,
        'compressed': compressed,
        'compression_ratio': ratio,
        'is_optimal': is_optimal
    }
    
    with open('data/game_state_compressed.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n" + "=" * 70)
    print("✓ Compression complete")
    print("✓ Saved to: data/game_state_compressed.json")
    print()
    print("⊢ Game state compressed from text to single integer ∎")

if __name__ == '__main__':
    main()
