#!/usr/bin/env python3
"""
Compute the Monster Brainrot Vector for a git repository
196,883-dimensional embedding via token@47 × line@59 × file@71
"""

import numpy as np
import subprocess
import hashlib
import re
from collections import defaultdict

def hash_to_shard(text, modulo):
    h = hashlib.sha256(text.encode()).digest()
    return int.from_bytes(h[:8], 'big') % modulo

def tokenize(line):
    return re.findall(r'\w+|[^\w\s]', line)

def compute_monster_vector():
    """Compute 196,883-dimensional Monster vector for repository"""
    
    print("🧠👹 Computing Monster Brainrot Vector")
    print("="*70)
    
    # Get files
    result = subprocess.run(['git', 'ls-files'], capture_output=True, text=True)
    files = [f for f in result.stdout.strip().split('\n') 
             if f.endswith(('.py', '.rs', '.md', '.lean'))][:20]
    
    # Initialize 3D tensor: [47, 59, 71]
    tensor = np.zeros((47, 59, 71), dtype=np.int32)
    
    total_triples = 0
    
    for filepath in files:
        try:
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
        except:
            continue
        
        file_shard = hash_to_shard(filepath, 71)
        
        for line in lines:
            if not line.strip():
                continue
            
            line_shard = hash_to_shard(line.strip(), 59)
            tokens = tokenize(line.strip())
            
            for token in tokens:
                if token.strip():
                    token_shard = hash_to_shard(token, 47)
                    tensor[token_shard, line_shard, file_shard] += 1
                    total_triples += 1
    
    # Flatten to 196,883-dimensional vector
    vector = tensor.flatten()
    
    # Statistics
    print(f"Files processed: {len(files)}")
    print(f"Total triples: {total_triples:,}")
    print(f"Vector dimensions: {len(vector):,}")
    print(f"Non-zero entries: {np.count_nonzero(vector):,}")
    print(f"Sparsity: {np.count_nonzero(vector)/len(vector)*100:.2f}%")
    print(f"L2 norm: {np.linalg.norm(vector):.2f}")
    print(f"Max value: {vector.max()}")
    print()
    
    # Top dimensions
    top_indices = np.argsort(vector)[-10:][::-1]
    print("🔥 Top 10 dimensions:")
    for idx in top_indices:
        # Decode back to (token, line, file) shards
        token_shard = idx // (59 * 71)
        line_shard = (idx // 71) % 59
        file_shard = idx % 71
        
        print(f"  Dim {idx:6d}: {vector[idx]:4d} | "
              f"token@{token_shard:2d} × line@{line_shard:2d} × file@{file_shard:2d}")
    
    print()
    print("💾 Saving vector...")
    
    # Save sparse representation
    nonzero = np.nonzero(vector)[0]
    sparse = {
        'dimensions': 196883,
        'nonzero_count': len(nonzero),
        'indices': nonzero.tolist()[:100],  # First 100
        'values': vector[nonzero].tolist()[:100],
        'norm': float(np.linalg.norm(vector)),
        'sparsity': float(np.count_nonzero(vector)/len(vector))
    }
    
    import json
    with open('monster_brainrot_vector.json', 'w') as f:
        json.dump(sparse, f, indent=2)
    
    print("✅ Saved to: monster_brainrot_vector.json")
    print()
    print("🐓🦅👹 Repository embedded in Monster space!")
    
    return vector

if __name__ == "__main__":
    compute_monster_vector()
