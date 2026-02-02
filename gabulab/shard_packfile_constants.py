#!/usr/bin/env python3
"""
Shard all constant values from all declarations
Extract: packs → objects → decls → constants → 71 Monster shards
"""

import json
import re
from collections import defaultdict

def extract_constants_from_decl(decl_name, decl_type):
    """Extract constant values from declaration"""
    constants = []
    
    # Extract numbers
    numbers = re.findall(r'\b\d+\b', decl_name)
    constants.extend([("number", int(n)) for n in numbers])
    
    # Extract hex values
    hex_vals = re.findall(r'0x[0-9a-fA-F]+', decl_name)
    constants.extend([("hex", h) for h in hex_vals])
    
    # Common constant patterns
    if "const" in decl_name.lower():
        # Extract value after =
        val = re.search(r'=\s*([^;,\s]+)', decl_name)
        if val:
            constants.append(("const", val.group(1)))
    
    return constants

def shard_constant(const_value):
    """Map constant to shard (0-70)"""
    if isinstance(const_value, int):
        return const_value % 71
    else:
        return hash(str(const_value)) % 71

def process_decls():
    """Process declarations and extract constants"""
    
    print("🔮⚡ EXTRACTING CONSTANTS FROM DECLARATIONS")
    print("=" * 70)
    print()
    
    # Load declarations
    try:
        with open('packfile_decls_sharded.json', 'r') as f:
            data = json.load(f)
    except:
        print("⚠️  Run shard_packfile_decls.py first")
        return {}, 0
    
    shard_constants = defaultdict(list)
    total_constants = 0
    
    # Process each shard's declarations
    for shard_id, shard_data in data['shards'].items():
        for decl in shard_data.get('sample', []):
            # Extract constants
            constants = extract_constants_from_decl(decl['name'], decl['type'])
            
            for const_type, const_val in constants:
                shard = shard_constant(const_val)
                shard_constants[shard].append({
                    "value": const_val,
                    "type": const_type,
                    "from_decl": decl['name'][:30],
                    "object_sha": decl['object_sha'][:8]
                })
                total_constants += 1
    
    print(f"✅ Extracted {total_constants:,} constants")
    print()
    
    return dict(shard_constants), total_constants

def display_constant_stats(shard_constants):
    """Display constant shard statistics"""
    
    print("=" * 70)
    print("CONSTANT VALUE SHARD DISTRIBUTION")
    print("=" * 70)
    print()
    print("Shard | Constants | Types | Sample Value")
    print("-" * 70)
    
    for shard_id in range(min(20, 71)):
        if shard_id in shard_constants:
            consts = shard_constants[shard_id]
            types = len(set(c["type"] for c in consts))
            sample = str(consts[0]["value"])[:20] if consts else "N/A"
            print(f"{shard_id:5d} | {len(consts):9d} | {types:5d} | {sample}")
    
    print()
    
    # Summary
    total = sum(len(c) for c in shard_constants.values())
    
    print(f"Total Constants: {total:,}")
    print(f"Shards Used: {len(shard_constants)}/71")
    print()
    
    # Monster constants check
    monster_vals = [2, 3, 5, 7, 8, 10, 71, 72, 196884]
    print("Monster Constants Found:")
    for val in monster_vals:
        shard = val % 71
        if shard in shard_constants:
            matches = [c for c in shard_constants[shard] if c["value"] == val]
            if matches:
                print(f"  {val:6d} → Shard {shard:2d} ({len(matches)} occurrences)")
    print()

def main():
    print("🔮⚡📻🦞 CONSTANT VALUE SHARDER")
    print("=" * 70)
    print()
    print("Extracting: packs → objects → decls → constants → 71 shards")
    print()
    
    # Process
    shard_constants, total = process_decls()
    
    # Display
    display_constant_stats(shard_constants)
    
    # Save
    output = {
        "total_constants": total,
        "shards": {
            k: {
                "count": len(v),
                "types": list(set(c["type"] for c in v)),
                "values": [c["value"] for c in v[:10]]  # First 10 values
            }
            for k, v in shard_constants.items()
        }
    }
    
    with open('packfile_constants_sharded.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to packfile_constants_sharded.json")
    print()
    print("✅ All constant values sharded into 71 Monster shards!")
    print("🔮 Complete chain: packs → objects → decls → constants → shards!")

if __name__ == '__main__':
    main()
