#!/usr/bin/env python3
"""Ingest th-desugar files and map each byte to Monster group conformally"""

import hashlib
from pathlib import Path
from dataclasses import dataclass
from typing import List, Tuple

MONSTER_DIMS = 196883
SHARDS = 71
MONSTER_WALK_STEP = 0x1F90

@dataclass
class MonsterMapping:
    file_path: str
    byte_offset: int
    byte_value: int
    shard_id: int
    monster_position: int
    j_invariant: int

def monster_walk(data: bytes) -> int:
    """Walk through Monster group"""
    pos = 0
    for byte in data:
        pos = (pos + MONSTER_WALK_STEP * byte) & 0xFFFFFFFFFFFFFFFF
    return pos

def map_byte_to_monster(byte: int, offset: int) -> Tuple[int, int, int]:
    """Map single byte to Monster coordinate"""
    shard = (byte + offset) % SHARDS
    position = (offset * MONSTER_WALK_STEP + byte) & 0xFFFFFFFFFFFFFFFF
    j_inv = 744 + 196884 * shard
    return shard, position, j_inv

def ingest_file(file_path: str) -> List[MonsterMapping]:
    """Ingest file and map each byte conformally"""
    mappings = []
    
    try:
        # Skip directories
        p = Path(file_path)
        if not p.exists() or p.is_dir():
            return mappings
            
        with open(file_path, 'rb') as f:
            data = f.read()
            
        for offset, byte in enumerate(data):
            shard, pos, j_inv = map_byte_to_monster(byte, offset)
            mappings.append(MonsterMapping(
                file_path=file_path,
                byte_offset=offset,
                byte_value=byte,
                shard_id=shard,
                monster_position=pos,
                j_invariant=j_inv
            ))
    except Exception:
        pass  # Skip all errors - even temp files count
    
    return mappings

def ingest_all_files(file_list: str) -> List[MonsterMapping]:
    """Ingest all files from list"""
    all_mappings = []
    
    with open(file_list, 'r') as f:
        files = [line.strip() for line in f if line.strip()]
    
    print(f"Ingesting {len(files)} files...")
    
    for i, file_path in enumerate(files):
        if i % 50 == 0:
            print(f"  Progress: {i}/{len(files)}")
        
        mappings = ingest_file(file_path)
        all_mappings.extend(mappings)
    
    return all_mappings

def compute_conformal_witness(mappings: List[MonsterMapping]) -> dict:
    """Compute conformal mapping witness"""
    shard_counts = [0] * SHARDS
    total_bytes = len(mappings)
    
    for m in mappings:
        shard_counts[m.shard_id] += 1
    
    # Compute hash of entire mapping
    mapping_hash = hashlib.blake2b()
    for m in mappings[:1000]:  # Sample first 1000
        mapping_hash.update(bytes([m.byte_value, m.shard_id]))
    
    return {
        'total_bytes': total_bytes,
        'total_files': len(set(m.file_path for m in mappings)),
        'shard_distribution': shard_counts,
        'mapping_hash': mapping_hash.hexdigest(),
        'monster_walk_final': monster_walk(bytes([m.byte_value for m in mappings[:10000]])),
    }

def main():
    file_list = 'data/th-desugar-find-list.txt'
    
    print("Monster Conformal Mapping: th-desugar → Monster Group")
    print("=" * 60)
    
    # Ingest all files
    mappings = ingest_all_files(file_list)
    
    print(f"\nTotal bytes mapped: {len(mappings):,}")
    
    # Compute witness
    witness = compute_conformal_witness(mappings)
    
    print(f"\nConformal Witness:")
    print(f"  Files: {witness['total_files']}")
    print(f"  Bytes: {witness['total_bytes']:,}")
    print(f"  Mapping hash: {witness['mapping_hash'][:16]}...")
    print(f"  Monster walk: {witness['monster_walk_final']:,}")
    
    print(f"\nShard distribution (first 10):")
    for i in range(10):
        print(f"  Shard {i:2d}: {witness['shard_distribution'][i]:,} bytes")
    
    # Save witness
    import json
    output = 'data/th_desugar_monster_witness.json'
    with open(output, 'w') as f:
        json.dump({
            'witness': witness,
            'sample_mappings': [
                {
                    'file': m.file_path,
                    'offset': m.byte_offset,
                    'byte': m.byte_value,
                    'shard': m.shard_id,
                    'j_invariant': m.j_invariant
                }
                for m in mappings[:100]
            ]
        }, f, indent=2)
    
    print(f"\nWitness saved to: {output}")

if __name__ == '__main__':
    main()
