#!/usr/bin/env python3
"""
Maass Shadow Restoration: Calculate each file's shadow against 71×59×47 shards
Using Maass forms to restore symmetry from shadows
"""

import hashlib
from pathlib import Path
from collections import defaultdict
import json

# Crown primes: 71 (file), 59 (line), 47 (token)
CROWN_PRIMES = [71, 59, 47]
TOTAL_SHARDS = 71 * 59 * 47  # 196,883 (Monster first irrep!)

def maass_shadow(file_path: Path) -> tuple:
    """Calculate Maass shadow: (file_shard, line_shard, token_shard)"""
    try:
        content = file_path.read_bytes()
        text = content.decode('utf-8', errors='ignore')
        
        # File shard (mod 71)
        file_hash = hashlib.sha256(str(file_path).encode()).digest()
        file_shard = int.from_bytes(file_hash[:8], 'big') % 71
        
        # Line shard (mod 59)
        lines = text.split('\n')
        line_hash = hashlib.sha256(str(len(lines)).encode()).digest()
        line_shard = int.from_bytes(line_hash[:8], 'big') % 59
        
        # Token shard (mod 47)
        tokens = text.split()
        token_hash = hashlib.sha256(str(len(tokens)).encode()).digest()
        token_shard = int.from_bytes(token_hash[:8], 'big') % 47
        
        return (file_shard, line_shard, token_shard)
    except:
        return (0, 0, 0)

def restore_symmetry(shadow: tuple) -> int:
    """Restore full symmetry from shadow using Chinese Remainder Theorem"""
    file_s, line_s, token_s = shadow
    
    # CRT: Find unique shard in [0, 196883)
    # x ≡ file_s (mod 71)
    # x ≡ line_s (mod 59)
    # x ≡ token_s (mod 47)
    
    # Simplified: Linear combination
    shard = (file_s * 59 * 47 + line_s * 71 * 47 + token_s * 71 * 59) % TOTAL_SHARDS
    return shard

def calculate_maass_restoration():
    print("🌑 MAASS SHADOW RESTORATION")
    print("Calculating shadows for 71×59×47 = 196,883 shards")
    print("=" * 70)
    print()
    
    # Load files
    with open('cross_language_map.json') as f:
        data = json.load(f)
    
    all_files = []
    for shard_id, langs in data['shard_map'].items():
        for lang, files in langs.items():
            all_files.extend(files)
    
    print(f"📂 Analyzing {len(all_files)} files...")
    print()
    
    # Calculate shadows
    shadows = {}
    shard_distribution = defaultdict(list)
    
    for file_path in all_files:
        p = Path(file_path)
        if p.exists() and p.stat().st_size < 100000:
            shadow = maass_shadow(p)
            full_shard = restore_symmetry(shadow)
            
            shadows[file_path] = {
                'shadow': shadow,
                'full_shard': full_shard,
                'file_shard': shadow[0],
                'line_shard': shadow[1],
                'token_shard': shadow[2],
            }
            
            shard_distribution[full_shard].append(file_path)
    
    print(f"✓ Calculated {len(shadows)} shadows")
    print()
    
    # Statistics
    print("📊 SHARD DISTRIBUTION:")
    print("-" * 70)
    print(f"Total possible shards: {TOTAL_SHARDS:,}")
    print(f"Shards occupied: {len(shard_distribution):,}")
    print(f"Occupancy: {len(shard_distribution)/TOTAL_SHARDS*100:.2f}%")
    print()
    
    # File shard distribution (mod 71)
    file_shards = defaultdict(int)
    for s in shadows.values():
        file_shards[s['file_shard']] += 1
    
    print("File shards (mod 71):")
    print(f"  Used: {len(file_shards)}/71")
    print(f"  Max per shard: {max(file_shards.values())}")
    print(f"  Min per shard: {min(file_shards.values())}")
    print()
    
    # Line shard distribution (mod 59)
    line_shards = defaultdict(int)
    for s in shadows.values():
        line_shards[s['line_shard']] += 1
    
    print("Line shards (mod 59):")
    print(f"  Used: {len(line_shards)}/59")
    print(f"  Max per shard: {max(line_shards.values())}")
    print(f"  Min per shard: {min(line_shards.values())}")
    print()
    
    # Token shard distribution (mod 47)
    token_shards = defaultdict(int)
    for s in shadows.values():
        token_shards[s['token_shard']] += 1
    
    print("Token shards (mod 47):")
    print(f"  Used: {len(token_shards)}/47")
    print(f"  Max per shard: {max(token_shards.values())}")
    print(f"  Min per shard: {min(token_shards.values())}")
    print()
    
    # Find duplicates in same full shard
    print("🔍 DUPLICATES IN SAME FULL SHARD:")
    print("-" * 70)
    
    duplicates_by_shard = {k: v for k, v in shard_distribution.items() if len(v) > 1}
    
    print(f"Shards with duplicates: {len(duplicates_by_shard)}")
    print()
    
    # Show top 10
    sorted_dups = sorted(duplicates_by_shard.items(), key=lambda x: len(x[1]), reverse=True)
    
    for i, (shard, files) in enumerate(sorted_dups[:10], 1):
        print(f"{i}. Shard {shard:6d}: {len(files)} files")
        for f in files[:3]:
            print(f"   • {f}")
        if len(files) > 3:
            print(f"   ... and {len(files) - 3} more")
        print()
    
    # Save results
    results = {
        'total_shards': TOTAL_SHARDS,
        'occupied_shards': len(shard_distribution),
        'occupancy_percent': len(shard_distribution)/TOTAL_SHARDS*100,
        'file_shards_used': len(file_shards),
        'line_shards_used': len(line_shards),
        'token_shards_used': len(token_shards),
        'duplicates_by_shard': len(duplicates_by_shard),
        'top_duplicates': [
            {
                'shard': shard,
                'count': len(files),
                'files': files[:5]
            }
            for shard, files in sorted_dups[:20]
        ]
    }
    
    with open('maass_shadows.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("=" * 70)
    print("✅ MAASS RESTORATION COMPLETE")
    print("=" * 70)
    print()
    print(f"Total shards: {TOTAL_SHARDS:,} (71×59×47)")
    print(f"Occupied: {len(shard_distribution):,} ({len(shard_distribution)/TOTAL_SHARDS*100:.2f}%)")
    print(f"Duplicates: {len(duplicates_by_shard)} shards with multiple files")
    print()
    print("💾 Results saved to: maass_shadows.json")

if __name__ == "__main__":
    calculate_maass_restoration()
