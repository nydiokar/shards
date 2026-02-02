#!/usr/bin/env python3
"""Parallel Lean file ingestion: 24 CPUs × 71 shards"""
import os
import json
from pathlib import Path
from multiprocessing import Pool
from collections import defaultdict

def hash_to_shard(path, num_shards=71):
    """Hash path to shard 0-70"""
    return hash(path) % num_shards

def analyze_file(path):
    """Analyze single Lean file"""
    try:
        with open(path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        return {
            'path': path,
            'shard': hash_to_shard(path),
            'lines': content.count('\n'),
            'theorem': 'theorem' in content,
            'def': 'def' in content,
            'inductive': 'inductive' in content,
        }
    except:
        return None

def main():
    input_file = Path.home() / 'introspector' / '.temp-find-lean.txt'
    output_dir = Path.home() / 'introspector' / 'lean_shards'
    output_dir.mkdir(exist_ok=True)
    
    print("📖 Reading paths...")
    with open(input_file) as f:
        lean_paths = [l.strip() for l in f if l.strip().endswith('.lean')]
    
    print(f"Found {len(lean_paths)} Lean files")
    print(f"Using 24 CPUs × 71 shards...")
    
    # Parallel processing
    with Pool(24) as pool:
        results = pool.map(analyze_file, lean_paths, chunksize=100)
    
    results = [r for r in results if r]
    
    # Distribute to 71 shards
    shards = defaultdict(list)
    for r in results:
        shards[r['shard']].append(r)
    
    # Save each shard
    stats = {'files': len(results), 'shards': {}}
    for shard_id in range(71):
        shard_data = shards[shard_id]
        shard_file = output_dir / f'shard_{shard_id:02d}.json'
        
        with open(shard_file, 'w') as f:
            json.dump(shard_data, f)
        
        stats['shards'][shard_id] = {
            'count': len(shard_data),
            'lines': sum(d['lines'] for d in shard_data),
            'theorems': sum(d['theorem'] for d in shard_data)
        }
        
        if len(shard_data) > 0:
            print(f"  Shard {shard_id:02d}: {len(shard_data)} files")
    
    # Save stats
    with open(output_dir / 'stats.json', 'w') as f:
        json.dump(stats, f, indent=2)
    
    print(f"\n✅ {len(results)} files → 71 shards")
    print(f"💾 {output_dir}/")

if __name__ == '__main__':
    main()
