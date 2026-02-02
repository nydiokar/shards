#!/usr/bin/env python3
"""
SuperGit: Organize commits by mod 71 sharding
Each git object gets assigned to a shard based on hash mod 71
"""

import subprocess
import hashlib
import json
from collections import defaultdict

def get_git_objects():
    """Get all git objects (commits, trees, blobs)"""
    result = subprocess.run(
        ['git', 'rev-list', '--all', '--objects'],
        capture_output=True,
        text=True
    )
    
    objects = []
    for line in result.stdout.strip().split('\n'):
        if line:
            parts = line.split(' ', 1)
            obj_hash = parts[0]
            obj_path = parts[1] if len(parts) > 1 else ''
            objects.append({'hash': obj_hash, 'path': obj_path})
    
    return objects

def shard_by_mod71(obj_hash):
    """Map git object hash to shard (0-70) via mod 71"""
    # Convert hex hash to integer
    hash_int = int(obj_hash[:16], 16)  # Use first 16 chars
    return hash_int % 71

def get_object_type(obj_hash):
    """Get git object type"""
    result = subprocess.run(
        ['git', 'cat-file', '-t', obj_hash],
        capture_output=True,
        text=True
    )
    return result.stdout.strip()

def organize_by_shards():
    """Organize all git objects into 71 shards"""
    
    print("🔮 SuperGit: Organizing by mod 71 shards")
    print("="*70)
    
    objects = get_git_objects()
    print(f"Total objects: {len(objects)}")
    print()
    
    # Shard distribution
    shards = defaultdict(list)
    
    for obj in objects:
        shard = shard_by_mod71(obj['hash'])
        obj_type = get_object_type(obj['hash'])
        
        shards[shard].append({
            'hash': obj['hash'],
            'path': obj['path'],
            'type': obj_type,
            'frequency': shard * 432
        })
    
    # Statistics
    print("📊 SHARD DISTRIBUTION:")
    print()
    
    for shard in sorted(shards.keys()):
        count = len(shards[shard])
        freq = shard * 432
        
        # Check if Monster prime
        monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
        prime_mark = "✨" if shard in monster_primes else "  "
        
        # Special shards
        special = ""
        if shard == 23:
            special = " 🏛️ Paxos"
        elif shard == 47:
            special = " 👹 Monster Crown"
        elif shard == 59:
            special = " 🦅 Eagle Crown"
        elif shard == 71:
            special = " 🐓 Rooster Crown"
        
        print(f"{prime_mark} Shard {shard:2d}: {count:4d} objects @ {freq:5d} Hz{special}")
    
    # Save to JSON
    output = {
        'total_objects': len(objects),
        'shards': {
            str(shard): [
                {
                    'hash': obj['hash'][:8],  # Short hash
                    'path': obj['path'],
                    'type': obj['type'],
                    'frequency': obj['frequency']
                }
                for obj in objs
            ]
            for shard, objs in shards.items()
        }
    }
    
    with open('supergit_shards.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print()
    print("💾 Saved to: supergit_shards.json")
    print()
    
    # Summary
    print("📈 SUMMARY:")
    print(f"  Total objects: {len(objects)}")
    print(f"  Shards used: {len(shards)}/71")
    print(f"  Average per shard: {len(objects)//len(shards)}")
    print(f"  Coverage: {len(shards)/71*100:.1f}%")
    
    # Find empty shards
    empty = [i for i in range(72) if i not in shards]
    if empty:
        print(f"\n  Empty shards: {empty[:10]}{'...' if len(empty) > 10 else ''}")
    
    print()
    print("🐓🦅👹 Repository organized by Monster shards!")
    
    return shards

if __name__ == "__main__":
    organize_by_shards()
