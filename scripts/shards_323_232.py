#!/usr/bin/env python3
"""71 Shards of 323/232: Mycelium Path Distribution"""
import json
from pathlib import Path

# The canonical pair
NODE_232 = 232
NODE_323 = 323

# 71 shards (Axiom of Completion)
NUM_SHARDS = 71

def shard_distribution(n, num_shards=71):
    """Distribute number across 71 shards"""
    base = n // num_shards
    remainder = n % num_shards
    
    shards = []
    for i in range(num_shards):
        shard_val = base + (1 if i < remainder else 0)
        shards.append({
            'shard_id': i,
            'value': shard_val,
            'mod_71': i,
            'is_rooster': i == 70
        })
    
    return shards

def analyze_323_shards():
    """Analyze 323 distributed across 71 shards"""
    
    print("🍄 323 ACROSS 71 SHARDS")
    print("="*80)
    
    # 323 / 71
    quotient = NODE_323 // NUM_SHARDS
    remainder = NODE_323 % NUM_SHARDS
    
    print(f"\n323 ÷ 71 = {quotient} remainder {remainder}")
    print(f"  Base: {quotient} per shard")
    print(f"  First {remainder} shards get +1")
    
    # Distribute
    shards = shard_distribution(NODE_323)
    
    # Find special shards
    print(f"\n🎯 SPECIAL SHARDS:")
    
    # Shards with extra
    extra_shards = [s for s in shards if s['value'] > quotient]
    print(f"  Shards with extra: {len(extra_shards)} (shards 0-{remainder-1})")
    
    # Rooster shard
    rooster = shards[70]
    print(f"  Rooster shard (71): value = {rooster['value']}")
    
    # BDI shards (mod 10 = 3)
    bdi_shards = [s for s in shards if s['shard_id'] % 10 == 3]
    print(f"  BDI shards (mod 10 = 3): {[s['shard_id'] for s in bdi_shards]}")
    print(f"    Values: {[s['value'] for s in bdi_shards]}")
    
    return shards

def analyze_232_shards():
    """Analyze 232 distributed across 71 shards"""
    
    print(f"\n🍄 232 ACROSS 71 SHARDS")
    print("="*80)
    
    # 232 / 71
    quotient = NODE_232 // NUM_SHARDS
    remainder = NODE_232 % NUM_SHARDS
    
    print(f"\n232 ÷ 71 = {quotient} remainder {remainder}")
    print(f"  Base: {quotient} per shard")
    print(f"  First {remainder} shards get +1")
    
    # Distribute
    shards = shard_distribution(NODE_232)
    
    # Find special shards
    print(f"\n🎯 SPECIAL SHARDS:")
    
    # Shards with extra
    extra_shards = [s for s in shards if s['value'] > quotient]
    print(f"  Shards with extra: {len(extra_shards)} (shards 0-{remainder-1})")
    
    # Rooster shard
    rooster = shards[70]
    print(f"  Rooster shard (71): value = {rooster['value']}")
    
    # BDI shards (mod 10 = 3)
    bdi_shards = [s for s in shards if s['shard_id'] % 10 == 3]
    print(f"  BDI shards (mod 10 = 3): {[s['shard_id'] for s in bdi_shards]}")
    print(f"    Values: {[s['value'] for s in bdi_shards]}")
    
    return shards

def mycelium_path_shards():
    """Analyze the path 232 ↔ 323 across shards"""
    
    print(f"\n🌱 MYCELIUM PATH ACROSS 71 SHARDS")
    print("="*80)
    
    shards_232 = shard_distribution(NODE_232)
    shards_323 = shard_distribution(NODE_323)
    
    # Compare shard by shard
    print(f"\nShard-by-Shard Comparison:")
    print(f"  Shard | 232 | 323 | Δ | Path")
    print(f"  ------|-----|-----|---|-----")
    
    for i in range(NUM_SHARDS):
        val_232 = shards_232[i]['value']
        val_323 = shards_323[i]['value']
        delta = val_323 - val_232
        
        # Only show interesting shards
        if i < 10 or i == 70 or i % 10 == 3:
            arrow = "→" if delta > 0 else "←" if delta < 0 else "="
            print(f"  {i:5d} | {val_232:3d} | {val_323:3d} | {delta:+2d} | {arrow}")
    
    print(f"  ...")
    
    # Total flow
    total_delta = sum(shards_323[i]['value'] - shards_232[i]['value'] for i in range(NUM_SHARDS))
    print(f"\n  Total flow: {total_delta:+d} (323 - 232 = {NODE_323 - NODE_232})")

def find_323_232_in_lean():
    """Search for 323 and 232 patterns in Lean corpus"""
    
    print(f"\n🔍 SEARCHING LEAN CORPUS:")
    print("="*80)
    
    # Load Lean data
    lean_data_file = Path.home() / 'introspector' / 'lean4_monster_body.json'
    
    if lean_data_file.exists():
        with open(lean_data_file) as f:
            data = json.load(f)
        
        lean_consts = data['lean_corpus']['constants']
        
        print(f"\nLean Constants: {lean_consts:,}")
        
        # 323 shards
        consts_per_323 = lean_consts // NODE_323
        print(f"\n323 Shards:")
        print(f"  {lean_consts:,} ÷ 323 = {consts_per_323:,} blocks")
        print(f"  Remainder: {lean_consts % NODE_323}")
        
        # 232 shards
        consts_per_232 = lean_consts // NODE_232
        print(f"\n232 Shards:")
        print(f"  {lean_consts:,} ÷ 232 = {consts_per_232:,} blocks")
        print(f"  Remainder: {lean_consts % NODE_232}")
        
        # Ratio
        ratio = consts_per_323 / consts_per_232
        print(f"\nRatio: {ratio:.6f}")
        print(f"  323/232 = {NODE_323/NODE_232:.6f}")
        print(f"  Close match!")
        
        # 71 shards of each
        print(f"\n71 Shards of 323-blocks:")
        blocks_323 = consts_per_323
        per_shard_323 = blocks_323 // NUM_SHARDS
        print(f"  {blocks_323:,} blocks ÷ 71 = {per_shard_323:,} per shard")
        
        print(f"\n71 Shards of 232-blocks:")
        blocks_232 = consts_per_232
        per_shard_232 = blocks_232 // NUM_SHARDS
        print(f"  {blocks_232:,} blocks ÷ 71 = {per_shard_232:,} per shard")

def main():
    print("🍄 71 SHARDS OF 323/232")
    print("   Mycelium Path Distribution Across Monster")
    print()
    
    # Analyze 323
    shards_323 = analyze_323_shards()
    
    # Analyze 232
    shards_232 = analyze_232_shards()
    
    # Path across shards
    mycelium_path_shards()
    
    # Search Lean
    find_323_232_in_lean()
    
    # The Hint
    print(f"\n" + "="*80)
    print(f"💡 THE HINT")
    print("="*80)
    print(f"\n323 and 232 are not just numbers—they are INSTRUCTIONS")
    print(f"for how to distribute structure across 71 shards.")
    print(f"\nEach shard receives:")
    print(f"  • 323 ÷ 71 = 4 remainder 39")
    print(f"  • 232 ÷ 71 = 3 remainder 19")
    print(f"\nThe mycelium path 232 ↔ 323 shows:")
    print(f"  • How to transition from 3-per-shard to 4-per-shard")
    print(f"  • Which shards get the extra unit")
    print(f"  • The flow pattern across Monster symmetry")
    
    print(f"\n🌱 This is the DISTRIBUTION PATTERN for:")
    print(f"  • Lean constants across shards")
    print(f"  • Vertex operators across VOA")
    print(f"  • Automorphic forms across conjugacy classes")
    
    # Save
    output = {
        'node_323': {
            'value': NODE_323,
            'per_shard': NODE_323 // NUM_SHARDS,
            'remainder': NODE_323 % NUM_SHARDS,
            'shards': shards_323[:10]  # First 10
        },
        'node_232': {
            'value': NODE_232,
            'per_shard': NODE_232 // NUM_SHARDS,
            'remainder': NODE_232 % NUM_SHARDS,
            'shards': shards_232[:10]  # First 10
        },
        'path': {
            'delta': NODE_323 - NODE_232,
            'ratio': NODE_323 / NODE_232
        }
    }
    
    output_file = Path.home() / 'introspector' / 'shards_323_232.json'
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n💾 Saved to {output_file}")
    print("\n🐓→🦅→👹→🍄→🌳  71 Shards Distributed")

if __name__ == '__main__':
    main()
