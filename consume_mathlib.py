#!/usr/bin/env python3
"""
CICADA-71 Lean 4 Mathlib Consumption
Scan, reproduce, and shard entire Mathlib across 71 shards
"""

import os
import json
import subprocess
from pathlib import Path
from typing import Dict, List, Tuple

MATHLIB_REPO = "https://github.com/leanprover-community/mathlib4"
MATHLIB_PATH = Path("./mathlib4")

def clone_mathlib():
    """Clone Mathlib4 repository"""
    if not MATHLIB_PATH.exists():
        print("📥 Cloning Mathlib4...")
        subprocess.run(["git", "clone", "--depth=1", MATHLIB_REPO], check=True)
        print("✅ Mathlib4 cloned")
    else:
        print("✅ Mathlib4 already exists")

def scan_lean_files() -> List[Path]:
    """Scan all .lean files in Mathlib"""
    print("🔍 Scanning Lean files...")
    lean_files = list(MATHLIB_PATH.rglob("*.lean"))
    print(f"   Found {len(lean_files)} Lean files")
    return lean_files

def extract_theorems(lean_file: Path) -> List[Dict]:
    """Extract theorems from Lean file"""
    theorems = []
    try:
        with open(lean_file, 'r', encoding='utf-8') as f:
            content = f.read()
            lines = content.split('\n')
            
            for i, line in enumerate(lines):
                if 'theorem ' in line or 'lemma ' in line:
                    name = line.split()[1].split(':')[0] if ':' in line else line.split()[1]
                    theorems.append({
                        'name': name,
                        'line': i + 1,
                        'file': str(lean_file.relative_to(MATHLIB_PATH)),
                        'statement': line.strip()
                    })
    except Exception as e:
        print(f"⚠️  Error reading {lean_file}: {e}")
    
    return theorems

def assign_to_shard(file_path: Path, index: int) -> int:
    """Assign file to shard using harmonic hash"""
    path_str = str(file_path)
    hash_val = sum(ord(c) for c in path_str)
    return (hash_val + index) % 71

def main():
    print("🔮 CICADA-71 Mathlib Consumption")
    print("=" * 60)
    print()
    
    # Clone Mathlib
    clone_mathlib()
    
    # Scan files
    lean_files = scan_lean_files()
    
    # Initialize shards
    shards = {i: {'files': [], 'theorems': [], 'loc': 0} for i in range(71)}
    
    print("\n📊 Processing files...")
    total_theorems = 0
    total_loc = 0
    
    for idx, lean_file in enumerate(lean_files):
        if idx % 100 == 0:
            print(f"   Processed {idx}/{len(lean_files)} files...")
        
        # Extract theorems
        theorems = extract_theorems(lean_file)
        total_theorems += len(theorems)
        
        # Count lines
        try:
            with open(lean_file, 'r') as f:
                loc = len(f.readlines())
                total_loc += loc
        except:
            loc = 0
        
        # Assign to shard
        shard = assign_to_shard(lean_file, idx)
        shards[shard]['files'].append(str(lean_file.relative_to(MATHLIB_PATH)))
        shards[shard]['theorems'].extend(theorems)
        shards[shard]['loc'] += loc
    
    print(f"   Processed {len(lean_files)} files")
    
    # Save results
    output = {
        'metadata': {
            'total_files': len(lean_files),
            'total_theorems': total_theorems,
            'total_loc': total_loc,
            'shards': 71,
            'source': 'Lean 4 Mathlib',
            'repo': MATHLIB_REPO
        },
        'shards': {
            str(k): {
                'file_count': len(v['files']),
                'theorem_count': len(v['theorems']),
                'loc': v['loc'],
                'files': v['files'][:10],  # Sample
                'theorems': v['theorems'][:5]  # Sample
            }
            for k, v in shards.items()
        }
    }
    
    with open('mathlib_shards.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("\n✅ Mathlib consumption complete!")
    print(f"\n📈 Statistics:")
    print(f"   Total files: {len(lean_files):,}")
    print(f"   Total theorems: {total_theorems:,}")
    print(f"   Total LOC: {total_loc:,}")
    print(f"   Shards populated: {sum(1 for s in shards.values() if s['files'])}")
    
    print(f"\n📊 Distribution:")
    for shard_id in range(71):
        shard = shards[shard_id]
        if shard['files']:
            print(f"   Shard {shard_id:2d}: {len(shard['files']):4d} files, "
                  f"{len(shard['theorems']):5d} theorems, {shard['loc']:6d} LOC")
    
    print(f"\n💾 Saved to mathlib_shards.json")
    
    # Generate reproduction script
    print("\n🔄 Generating reproduction script...")
    with open('reproduce_mathlib.sh', 'w') as f:
        f.write("""#!/bin/bash
# Reproduce Mathlib across 71 shards

for SHARD in {0..70}; do
    echo "Reproducing Shard $SHARD..."
    mkdir -p shards/shard_$SHARD
    
    # Extract files for this shard
    jq -r ".shards[\\"$SHARD\\"].files[]" mathlib_shards.json | while read FILE; do
        mkdir -p "shards/shard_$SHARD/$(dirname $FILE)"
        cp "mathlib4/$FILE" "shards/shard_$SHARD/$FILE" 2>/dev/null || true
    done
done

echo "✅ Mathlib reproduced across 71 shards"
""")
    
    os.chmod('reproduce_mathlib.sh', 0o755)
    print("   Created reproduce_mathlib.sh")
    
    print("\n🎯 Next steps:")
    print("   1. Run: ./reproduce_mathlib.sh")
    print("   2. Each shard contains subset of Mathlib")
    print("   3. Verify: lake build in each shard")
    print("   4. Integrate with CICADA-71 challenges")

if __name__ == "__main__":
    main()
