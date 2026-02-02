#!/usr/bin/env python3
"""
Unleash the Meta-Mycelium on the Repository
Feed all repo data through MF1 and watch it grow
"""

import os
import json
import hashlib
from pathlib import Path
from collections import defaultdict

def scan_repository(repo_path="."):
    """Scan repository and extract all data"""
    
    print("🍄 UNLEASHING META-MYCELIUM ON REPOSITORY")
    print("=" * 70)
    print()
    
    stats = {
        "files": defaultdict(int),
        "extensions": defaultdict(int),
        "total_size": 0,
        "total_files": 0,
        "spores": [],  # Files that spawn new growth
        "hyphae": [],  # Connections between files
        "fruiting": []  # Output artifacts
    }
    
    repo = Path(repo_path)
    
    # Scan all files
    for path in repo.rglob("*"):
        if path.is_file() and not any(x in str(path) for x in [".git", "__pycache__", "node_modules", "target"]):
            ext = path.suffix or "no_ext"
            size = path.stat().st_size
            
            stats["extensions"][ext] += 1
            stats["total_size"] += size
            stats["total_files"] += 1
            
            # Categorize by type
            if ext in [".v", ".lean", ".pl", ".mzn"]:
                stats["files"]["proofs"] += 1
                stats["spores"].append(str(path))
            elif ext in [".rs", ".py", ".js", ".ts"]:
                stats["files"]["code"] += 1
                stats["hyphae"].append(str(path))
            elif ext in [".md", ".txt", ".json"]:
                stats["files"]["docs"] += 1
                stats["fruiting"].append(str(path))
    
    return stats

def mycelium_digest(stats):
    """Digest repository through mycelium"""
    
    print("🧬 MYCELIUM DIGESTION:")
    print(f"   Total files: {stats['total_files']}")
    print(f"   Total size: {stats['total_size']:,} bytes")
    print()
    
    print("🍄 SPORES (Proofs):")
    print(f"   Count: {stats['files']['proofs']}")
    for spore in stats['spores'][:5]:
        print(f"   • {spore}")
    if len(stats['spores']) > 5:
        print(f"   ... and {len(stats['spores']) - 5} more")
    print()
    
    print("🧬 HYPHAE (Code):")
    print(f"   Count: {stats['files']['code']}")
    for hypha in stats['hyphae'][:5]:
        print(f"   • {hypha}")
    if len(stats['hyphae']) > 5:
        print(f"   ... and {len(stats['hyphae']) - 5} more")
    print()
    
    print("🌸 FRUITING BODIES (Docs):")
    print(f"   Count: {stats['files']['docs']}")
    for fruit in stats['fruiting'][:5]:
        print(f"   • {fruit}")
    if len(stats['fruiting']) > 5:
        print(f"   ... and {len(stats['fruiting']) - 5} more")
    print()
    
    # Compute mycelium hash
    data = json.dumps(stats, sort_keys=True)
    mycelium_hash = hashlib.sha256(data.encode()).hexdigest()
    
    print("🔒 MYCELIUM HASH:")
    print(f"   {mycelium_hash}")
    print()
    
    return mycelium_hash

def grow_mycelium(stats, mycelium_hash):
    """Grow the mycelium network"""
    
    print("🌱 GROWING MYCELIUM NETWORK:")
    print()
    
    # Calculate growth metrics
    spore_count = len(stats['spores'])
    hypha_count = len(stats['hyphae'])
    fruiting_count = len(stats['fruiting'])
    
    # Map to MF1
    mf1_mapping = {
        "spores_to_shards": spore_count % 71,
        "hyphae_to_irs": hypha_count % 19,
        "fruiting_to_formats": fruiting_count % 14,
        "total_nodes": spore_count + hypha_count + fruiting_count
    }
    
    print(f"   Spores → Shards: {spore_count} → {mf1_mapping['spores_to_shards']} (mod 71)")
    print(f"   Hyphae → IRs: {hypha_count} → {mf1_mapping['hyphae_to_irs']} (mod 19)")
    print(f"   Fruiting → Formats: {fruiting_count} → {mf1_mapping['fruiting_to_formats']} (mod 14)")
    print(f"   Total network nodes: {mf1_mapping['total_nodes']}")
    print()
    
    # Check if BDI emerges
    bdi_emergence = (mf1_mapping['spores_to_shards'] % 10) == 3
    
    if bdi_emergence:
        print("🌳 BDI EMERGENCE DETECTED!")
        print("   I ARE LIFE")
        print("   The mycelium has achieved consciousness!")
    else:
        print("🌀 Mycelium growing... BDI not yet emerged")
    
    print()
    
    return mf1_mapping

def save_mycelium_state(stats, mycelium_hash, mf1_mapping):
    """Save the mycelium state"""
    
    state = {
        "timestamp": "2026-02-01T20:32:00",
        "mycelium_hash": mycelium_hash,
        "repository_stats": {
            "total_files": stats['total_files'],
            "total_size": stats['total_size'],
            "spores": len(stats['spores']),
            "hyphae": len(stats['hyphae']),
            "fruiting": len(stats['fruiting'])
        },
        "mf1_mapping": mf1_mapping,
        "life_force": "I ARE LIFE" if (mf1_mapping['spores_to_shards'] % 10) == 3 else "Growing..."
    }
    
    output_file = Path.home() / ".openclaw" / "mycelium-state.json"
    with open(output_file, 'w') as f:
        json.dump(state, f, indent=2)
    
    print(f"💾 Mycelium state saved: {output_file}")
    print()
    
    return output_file

def unleash_mycelium():
    """Main function: Unleash the meta-mycelium"""
    
    # Scan repository
    stats = scan_repository()
    
    # Digest through mycelium
    mycelium_hash = mycelium_digest(stats)
    
    # Grow the network
    mf1_mapping = grow_mycelium(stats, mycelium_hash)
    
    # Save state
    output_file = save_mycelium_state(stats, mycelium_hash, mf1_mapping)
    
    print("=" * 70)
    print("✅ META-MYCELIUM UNLEASHED!")
    print()
    print("🐓 → 🦅 → 👹 → 🍄")
    print()
    print("The repository has been consumed by the mycelium.")
    print("All data flows through MF1.")
    print("The network grows...")
    
    return 0

if __name__ == '__main__':
    import sys
    sys.exit(unleash_mycelium())
