#!/usr/bin/env python3
"""Apply 15 Hecke operators via 9 Muses to bless all code artifacts, create zkwitnesses"""

import os
import hashlib
import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List

SHARDS = 71
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
MUSES = ["Calliope","Clio","Erato","Euterpe","Melpomene","Polyhymnia","Terpsichore","Thalia","Urania"]

@dataclass
class HeckeBlessing:
    """Hecke operator blessing via Muse"""
    artifact_type: str  # constant, term, expr, decl, module, file, dir, pack, blob, commit
    path: str
    hash: str
    shard: int
    muse: str
    hecke_prime: int
    j_invariant: int
    blessing: str

def hash_artifact(data: str) -> str:
    return hashlib.sha256(data.encode()).hexdigest()

def apply_hecke(artifact_hash: str, artifact_type: str, path: str) -> HeckeBlessing:
    """Apply Hecke operator T_p via Muse blessing"""
    h = int(artifact_hash[:16], 16)
    shard = h % SHARDS
    muse_idx = shard % 9
    prime_idx = shard % 15
    
    muse = MUSES[muse_idx]
    hecke_prime = PRIMES[prime_idx]
    j_inv = 744 + 196884 * shard
    blessing = f"T_{hecke_prime} via {muse}"
    
    return HeckeBlessing(
        artifact_type=artifact_type,
        path=path,
        hash=artifact_hash,
        shard=shard,
        muse=muse,
        hecke_prime=hecke_prime,
        j_invariant=j_inv,
        blessing=blessing
    )

def bless_file(filepath: Path) -> List[HeckeBlessing]:
    """Bless file and all its artifacts"""
    blessings = []
    
    try:
        content = filepath.read_text()
        
        # File level
        file_hash = hash_artifact(str(filepath) + content[:100])
        blessings.append(apply_hecke(file_hash, "file", str(filepath)))
        
        # Lines as terms
        for i, line in enumerate(content.split('\n')[:10]):  # First 10 lines
            if line.strip():
                line_hash = hash_artifact(line)
                blessings.append(apply_hecke(line_hash, "term", f"{filepath}:{i+1}"))
        
    except:
        pass
    
    return blessings

def bless_directory(dirpath: Path, max_files: int = 20) -> List[HeckeBlessing]:
    """Bless directory tree"""
    blessings = []
    
    # Directory itself
    dir_hash = hash_artifact(str(dirpath))
    blessings.append(apply_hecke(dir_hash, "dir", str(dirpath)))
    
    # Files in directory
    files = list(dirpath.glob("*"))[:max_files]
    for f in files:
        if f.is_file():
            blessings.extend(bless_file(f))
    
    return blessings

def bless_git_artifacts(repo_path: Path) -> List[HeckeBlessing]:
    """Bless git commits, blobs, packs"""
    blessings = []
    git_dir = repo_path / ".git"
    
    if not git_dir.exists():
        return blessings
    
    # HEAD commit
    try:
        head = (git_dir / "HEAD").read_text().strip()
        head_hash = hash_artifact(head)
        blessings.append(apply_hecke(head_hash, "commit", "HEAD"))
    except:
        pass
    
    # Refs
    refs_dir = git_dir / "refs" / "heads"
    if refs_dir.exists():
        for ref in list(refs_dir.glob("*"))[:5]:
            ref_hash = hash_artifact(ref.read_text())
            blessings.append(apply_hecke(ref_hash, "ref", str(ref.name)))
    
    # Pack files
    pack_dir = git_dir / "objects" / "pack"
    if pack_dir.exists():
        for pack in list(pack_dir.glob("*.pack"))[:3]:
            pack_hash = hash_artifact(str(pack.stat().st_size))
            blessings.append(apply_hecke(pack_hash, "pack", str(pack.name)))
    
    return blessings

def create_zkwitness(blessings: List[HeckeBlessing]) -> dict:
    """Create zero-knowledge witness from blessings"""
    
    # Aggregate by muse
    muse_counts = {m: 0 for m in MUSES}
    prime_counts = {p: 0 for p in PRIMES}
    
    for b in blessings:
        muse_counts[b.muse] += 1
        prime_counts[b.hecke_prime] += 1
    
    # Merkle root (simplified)
    all_hashes = [b.hash for b in blessings]
    merkle_root = hash_artifact(''.join(all_hashes))
    
    return {
        'merkle_root': merkle_root,
        'total_blessings': len(blessings),
        'muse_distribution': muse_counts,
        'hecke_distribution': prime_counts,
        'witness_type': 'hecke_muse_blessing',
        'shards_covered': len(set(b.shard for b in blessings)),
        'j_invariant_sum': sum(b.j_invariant for b in blessings)
    }

def main():
    print("15 Hecke Operators × 9 Muses: Blessing All Artifacts")
    print("=" * 70)
    print()
    
    # Bless Terpsichore shard
    terp_path = Path("shard06-terpsichore")
    
    if not terp_path.exists():
        print("Error: shard06-terpsichore not found")
        return
    
    print("Blessing shard06-terpsichore...")
    blessings = bless_directory(terp_path, max_files=10)
    
    # Bless git artifacts
    print("Blessing git artifacts...")
    blessings.extend(bless_git_artifacts(Path(".")))
    
    print(f"✓ Created {len(blessings)} blessings")
    print()
    
    # Show sample blessings
    print("Sample Blessings:")
    print(f"{'Type':<10} {'Muse':<12} {'Hecke':<8} {'Shard':<6} {'Path':<30}")
    print("-" * 70)
    
    for b in blessings[:15]:
        path_short = b.path[-30:] if len(b.path) > 30 else b.path
        print(f"{b.artifact_type:<10} {b.muse:<12} T_{b.hecke_prime:<6} {b.shard:<6} {path_short:<30}")
    
    # Create zkwitness
    print("\n" + "=" * 70)
    print("Creating zkWitness...")
    witness = create_zkwitness(blessings)
    
    print(f"\nzkWitness:")
    print(f"  Merkle Root: {witness['merkle_root'][:16]}...")
    print(f"  Total Blessings: {witness['total_blessings']}")
    print(f"  Shards Covered: {witness['shards_covered']}/71")
    print(f"  j-invariant Sum: {witness['j_invariant_sum']:,}")
    
    print("\n  Muse Distribution:")
    for muse, count in sorted(witness['muse_distribution'].items(), key=lambda x: x[1], reverse=True):
        if count > 0:
            print(f"    {muse:<12}: {count}")
    
    print("\n  Hecke Operator Distribution:")
    for prime, count in sorted(witness['hecke_distribution'].items(), key=lambda x: x[1], reverse=True)[:5]:
        if count > 0:
            print(f"    T_{prime:<3}: {count}")
    
    # Save
    output = {
        'witness': witness,
        'blessings': [asdict(b) for b in blessings[:100]],  # First 100
        'total': len(blessings)
    }
    
    with open('data/hecke_muse_zkwitness.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n" + "=" * 70)
    print("zkWitness saved to: data/hecke_muse_zkwitness.json")
    print()
    print("Every artifact blessed by:")
    print("  • 15 Hecke operators (Monster primes)")
    print("  • 9 Muses (Greek divine inspiration)")
    print("  • 71 Monster shards")
    print("  • j-invariant (Moonshine connection)")

if __name__ == '__main__':
    main()
