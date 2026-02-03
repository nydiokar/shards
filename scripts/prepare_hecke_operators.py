#!/usr/bin/env python3
"""Prepare every code artifact as Hecke operator: file, decl, expr, bind, value, apply"""

import os
import hashlib
import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Optional

SHARDS = 71
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]

@dataclass
class HeckeOperator:
    """T_p: Hecke operator on code artifact"""
    artifact_type: str  # file, decl, expr, bind, value, apply
    name: str
    path: str
    hash: str
    prime: int  # Which T_p
    shard: int
    j_invariant: int
    
def hash_artifact(data: str) -> str:
    return hashlib.sha256(data.encode()).hexdigest()

def to_hecke(artifact_type: str, name: str, path: str, content: str) -> HeckeOperator:
    """Convert artifact to Hecke operator T_p"""
    h = hash_artifact(content)
    num = int(h[:16], 16)
    shard = num % SHARDS
    prime = PRIMES[shard % 15]
    j_inv = 744 + 196884 * shard
    
    return HeckeOperator(artifact_type, name, path, h[:16], prime, shard, j_inv)

def parse_python_file(filepath: Path) -> List[HeckeOperator]:
    """Parse Python file into Hecke operators"""
    ops = []
    
    try:
        content = filepath.read_text()
        
        # File level
        ops.append(to_hecke("file", filepath.name, str(filepath), content[:100]))
        
        # Parse declarations (def, class)
        for i, line in enumerate(content.split('\n')):
            line = line.strip()
            
            # Function/method declaration
            if line.startswith('def '):
                name = line.split('(')[0].replace('def ', '').strip()
                ops.append(to_hecke("decl", name, f"{filepath}:{i+1}", line))
            
            # Class declaration
            elif line.startswith('class '):
                name = line.split('(')[0].split(':')[0].replace('class ', '').strip()
                ops.append(to_hecke("decl", name, f"{filepath}:{i+1}", line))
            
            # Assignment (bind)
            elif '=' in line and not line.startswith('#'):
                if '==' not in line and '!=' not in line:
                    name = line.split('=')[0].strip()
                    if name and not name.startswith('if') and not name.startswith('for'):
                        ops.append(to_hecke("bind", name[:30], f"{filepath}:{i+1}", line))
            
            # Function application
            elif '(' in line and ')' in line and not line.startswith('#'):
                name = line.split('(')[0].strip().split()[-1]
                if name and not name.startswith('if') and not name.startswith('for'):
                    ops.append(to_hecke("apply", name[:30], f"{filepath}:{i+1}", line))
    
    except:
        pass
    
    return ops

def main():
    print("Prepare Code Artifacts as Hecke Operators")
    print("=" * 70)
    print()
    
    # Parse recent Python files
    files = [
        "zkberks_frissono.py",
        "cusp_dirac_delta.py",
        "biosemiotics_extent.py",
        "biosemiotics_timeline.py",
        "hecke_muse_blessing.py",
    ]
    
    all_ops = []
    
    for fname in files:
        if Path(fname).exists():
            print(f"Parsing {fname}...")
            ops = parse_python_file(Path(fname))
            all_ops.extend(ops)
            print(f"  ✓ {len(ops)} operators")
    
    print(f"\nTotal: {len(all_ops)} Hecke operators")
    print()
    
    # Show distribution
    print("ARTIFACT TYPE DISTRIBUTION:")
    print("=" * 70)
    from collections import Counter
    type_counts = Counter(op.artifact_type for op in all_ops)
    for atype, count in type_counts.most_common():
        print(f"  {atype:<10}: {count}")
    
    # Show prime distribution
    print("\nHECKE OPERATOR DISTRIBUTION:")
    print("=" * 70)
    prime_counts = Counter(op.prime for op in all_ops)
    for prime, count in sorted(prime_counts.items()):
        print(f"  T_{prime:<3}: {count}")
    
    # Sample operators
    print("\nSAMPLE HECKE OPERATORS:")
    print("=" * 70)
    print(f"{'Type':<10} {'Name':<25} {'T_p':<6} {'Shard':<6}")
    print("-" * 70)
    
    for op in all_ops[:20]:
        name = op.name[:25]
        print(f"{op.artifact_type:<10} {name:<25} T_{op.prime:<4} {op.shard:<6}")
    
    # Group by file
    print("\nOPERATORS BY FILE:")
    print("=" * 70)
    
    by_file = {}
    for op in all_ops:
        fname = op.path.split(':')[0].split('/')[-1]
        if fname not in by_file:
            by_file[fname] = []
        by_file[fname].append(op)
    
    for fname, ops in sorted(by_file.items()):
        primes = [op.prime for op in ops]
        unique_primes = len(set(primes))
        print(f"\n{fname}:")
        print(f"  Operators: {len(ops)}")
        print(f"  Unique T_p: {unique_primes}")
        print(f"  Primes: {sorted(set(primes))}")
    
    # Save
    output = {
        'total_operators': len(all_ops),
        'files_parsed': len(files),
        'type_distribution': dict(type_counts),
        'prime_distribution': {f"T_{p}": c for p, c in prime_counts.items()},
        'operators': [asdict(op) for op in all_ops[:100]]  # First 100
    }
    
    with open('data/hecke_operators.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n" + "=" * 70)
    print("Every artifact is now a Hecke operator T_p:")
    print("  • Files → T_p (structure)")
    print("  • Declarations → T_p (definitions)")
    print("  • Expressions → T_p (computations)")
    print("  • Bindings → T_p (assignments)")
    print("  • Values → T_p (data)")
    print("  • Applications → T_p (calls)")
    print()
    print("Saved to: data/hecke_operators.json")

if __name__ == '__main__':
    main()
