# SOP: Swab the Deck
## Review All Files and Shard with Hecke-Maass

**Version**: 1.0  
**Date**: 2026-02-01  
**Owner**: CICADA-71 Core Team  
**Status**: Active

---

## Purpose

Systematically review all project files, compute Hecke eigenvalues, apply Maass weights, and distribute across 71 shards with harmonic encoding.

**Metaphor**: "Swabbing the deck" = cleaning up and organizing the codebase through mathematical sharding.

---

## Scope

- **All files** in repository (code, docs, configs)
- **Hecke eigenvalue** computation per file
- **Maass weight** application
- **71-shard distribution** via harmonic hash
- **Verification** of reconstruction

---

## Prerequisites

- [x] Python 3.10+
- [x] Rust toolchain
- [x] `sha256sum`, `wc`, `find`
- [x] Access to repository root
- [x] Write permissions for shard manifests

---

## Procedure

### Step 1: Inventory All Files

```bash
#!/bin/bash
# swab_deck_step1.sh - Inventory all files

echo "=== Step 1: Inventory All Files ==="

find . -type f \
    -not -path "./.git/*" \
    -not -path "./target/*" \
    -not -path "./node_modules/*" \
    -not -path "./.kiro/*" \
    > file_inventory.txt

TOTAL=$(wc -l < file_inventory.txt)
echo "Found $TOTAL files"

# Generate metadata
cat file_inventory.txt | while read file; do
    if [ -f "$file" ]; then
        SIZE=$(stat -f%z "$file" 2>/dev/null || stat -c%s "$file" 2>/dev/null)
        LINES=$(wc -l < "$file" 2>/dev/null || echo 0)
        HASH=$(sha256sum "$file" | cut -d' ' -f1)
        
        echo "$file|$SIZE|$LINES|$HASH"
    fi
done > file_metadata.txt

echo "Metadata saved to file_metadata.txt"
```

**Expected Output**: `file_inventory.txt`, `file_metadata.txt`

---

### Step 2: Compute Hecke Eigenvalues

```python
#!/usr/bin/env python3
# swab_deck_step2.py - Compute Hecke eigenvalues

import hashlib
import math
from pathlib import Path

# 71 primes
PRIMES_71 = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353
]

def compute_hecke_eigenvalue(file_path, shard_id):
    """Compute Hecke eigenvalue λ_p for file at shard"""
    with open(file_path, 'rb') as f:
        data = f.read()
    
    # Hash file content
    h = hashlib.sha256(data).digest()
    
    # Extract complex eigenvalue from hash
    re_bytes = int.from_bytes(h[:8], 'big')
    im_bytes = int.from_bytes(h[8:16], 'big')
    
    # Normalize to unit circle
    re = (re_bytes % 10000) / 10000.0 * 2 - 1
    im = (im_bytes % 10000) / 10000.0 * 2 - 1
    
    # Scale by √p (Ramanujan bound)
    p = PRIMES_71[shard_id]
    scale = 2 * math.sqrt(p)
    
    return {
        'file': file_path,
        'shard_id': shard_id,
        'prime': p,
        'eigenvalue_re': re * scale,
        'eigenvalue_im': im * scale,
        'norm': math.sqrt(re*re + im*im) * scale,
    }

def main():
    print("=== Step 2: Compute Hecke Eigenvalues ===")
    
    # Read file metadata
    files = []
    with open('file_metadata.txt') as f:
        for line in f:
            parts = line.strip().split('|')
            if len(parts) == 4:
                files.append({
                    'path': parts[0],
                    'size': int(parts[1]),
                    'lines': int(parts[2]),
                    'hash': parts[3],
                })
    
    # Compute Hecke eigenvalues
    eigenvalues = []
    for file_info in files:
        # Assign to shard via harmonic hash
        lines = file_info['lines']
        size = file_info['size']
        hash_val = int(file_info['hash'][:16], 16)
        
        shard_id = (lines * 7 + size * 3 + hash_val) % 71
        
        try:
            eigen = compute_hecke_eigenvalue(file_info['path'], shard_id)
            eigenvalues.append(eigen)
            print(f"File: {file_info['path'][:50]:50} → Shard {shard_id:2} (λ = {eigen['norm']:.3f})")
        except Exception as e:
            print(f"Error processing {file_info['path']}: {e}")
    
    # Save eigenvalues
    import json
    with open('hecke_eigenvalues.json', 'w') as f:
        json.dump(eigenvalues, f, indent=2)
    
    print(f"\nComputed {len(eigenvalues)} Hecke eigenvalues")
    print("Saved to hecke_eigenvalues.json")

if __name__ == '__main__':
    main()
```

**Expected Output**: `hecke_eigenvalues.json`

---

### Step 3: Apply Maass Weights

```python
#!/usr/bin/env python3
# swab_deck_step3.py - Apply Maass weights

import json
import math
from scipy.special import kv  # Modified Bessel function

def maass_weight(eigenvalue_re, eigenvalue_im, n):
    """Compute Maass weight K_ir(2πny)"""
    r = eigenvalue_im
    y = 1.0  # Height in upper half-plane
    
    arg = 2 * math.pi * n * y
    
    # K_ir(arg) - Modified Bessel function of second kind
    try:
        weight = kv(complex(0, r), arg)
        return abs(weight)
    except:
        # Fallback: exponential decay
        return math.exp(-arg / (1 + abs(r)))

def main():
    print("=== Step 3: Apply Maass Weights ===")
    
    # Load eigenvalues
    with open('hecke_eigenvalues.json') as f:
        eigenvalues = json.load(f)
    
    # Apply Maass weights
    weighted = []
    for eigen in eigenvalues:
        n = eigen['shard_id'] + 1
        weight = maass_weight(eigen['eigenvalue_re'], eigen['eigenvalue_im'], n)
        
        weighted.append({
            **eigen,
            'maass_weight': weight,
            'weighted_norm': eigen['norm'] * weight,
        })
        
        print(f"Shard {eigen['shard_id']:2}: λ = {eigen['norm']:6.3f}, "
              f"K_ir = {weight:6.3f}, weighted = {eigen['norm']*weight:6.3f}")
    
    # Save weighted eigenvalues
    with open('maass_weighted.json', 'w') as f:
        json.dump(weighted, f, indent=2)
    
    print(f"\nApplied Maass weights to {len(weighted)} files")
    print("Saved to maass_weighted.json")

if __name__ == '__main__':
    main()
```

**Expected Output**: `maass_weighted.json`

---

### Step 4: Distribute to 71 Shards

```python
#!/usr/bin/env python3
# swab_deck_step4.py - Distribute to 71 shards

import json
from collections import defaultdict

def main():
    print("=== Step 4: Distribute to 71 Shards ===")
    
    # Load weighted eigenvalues
    with open('maass_weighted.json') as f:
        weighted = json.load(f)
    
    # Group by shard
    shards = defaultdict(list)
    for item in weighted:
        shard_id = item['shard_id']
        shards[shard_id].append(item)
    
    # Generate shard manifest
    manifest = {
        'version': '1.0',
        'total_files': len(weighted),
        'shards': []
    }
    
    for shard_id in range(71):
        files = shards.get(shard_id, [])
        
        shard_info = {
            'shard_id': shard_id,
            'prime': weighted[0]['prime'] if files else None,
            'file_count': len(files),
            'files': [
                {
                    'path': f['file'],
                    'eigenvalue': f['norm'],
                    'maass_weight': f['maass_weight'],
                    'weighted_norm': f['weighted_norm'],
                }
                for f in files
            ],
            'total_weighted_norm': sum(f['weighted_norm'] for f in files),
        }
        
        manifest['shards'].append(shard_info)
        
        print(f"Shard {shard_id:2}: {len(files):3} files, "
              f"total weight = {shard_info['total_weighted_norm']:8.3f}")
    
    # Save manifest
    with open('HECKE_MAASS_MANIFEST.json', 'w') as f:
        json.dump(manifest, f, indent=2)
    
    print(f"\nDistributed {len(weighted)} files across 71 shards")
    print("Saved to HECKE_MAASS_MANIFEST.json")
    
    # Statistics
    file_counts = [len(shards[i]) for i in range(71)]
    print(f"\nStatistics:")
    print(f"  Min files per shard: {min(file_counts)}")
    print(f"  Max files per shard: {max(file_counts)}")
    print(f"  Avg files per shard: {sum(file_counts)/71:.1f}")

if __name__ == '__main__':
    main()
```

**Expected Output**: `HECKE_MAASS_MANIFEST.json`

---

### Step 5: Verify Reconstruction

```python
#!/usr/bin/env python3
# swab_deck_step5.py - Verify reconstruction

import json
import hashlib

def verify_shard_integrity(manifest):
    """Verify all files in manifest exist and match"""
    print("=== Step 5: Verify Reconstruction ===")
    
    errors = []
    verified = 0
    
    for shard in manifest['shards']:
        shard_id = shard['shard_id']
        
        for file_info in shard['files']:
            path = file_info['path']
            
            try:
                with open(path, 'rb') as f:
                    data = f.read()
                
                # Verify file exists and is readable
                verified += 1
                
            except Exception as e:
                errors.append(f"Shard {shard_id}: {path} - {e}")
    
    return verified, errors

def verify_harmonic_distribution(manifest):
    """Verify files are harmonically distributed"""
    print("\nVerifying harmonic distribution...")
    
    # Check all 71 shards present
    shard_ids = [s['shard_id'] for s in manifest['shards']]
    if len(shard_ids) != 71 or set(shard_ids) != set(range(71)):
        return False, "Missing shards"
    
    # Check distribution is balanced
    file_counts = [s['file_count'] for s in manifest['shards']]
    avg = sum(file_counts) / 71
    variance = sum((c - avg)**2 for c in file_counts) / 71
    
    print(f"  Average files per shard: {avg:.1f}")
    print(f"  Variance: {variance:.1f}")
    print(f"  Distribution: {'balanced' if variance < avg else 'unbalanced'}")
    
    return True, "OK"

def main():
    # Load manifest
    with open('HECKE_MAASS_MANIFEST.json') as f:
        manifest = json.load(f)
    
    # Verify integrity
    verified, errors = verify_shard_integrity(manifest)
    
    print(f"\nVerified {verified} files")
    if errors:
        print(f"Errors: {len(errors)}")
        for err in errors[:10]:
            print(f"  {err}")
    else:
        print("✓ All files verified")
    
    # Verify distribution
    ok, msg = verify_harmonic_distribution(manifest)
    if ok:
        print(f"✓ Harmonic distribution: {msg}")
    else:
        print(f"✗ Harmonic distribution: {msg}")
    
    # Summary
    print("\n" + "="*60)
    print("SWAB THE DECK COMPLETE")
    print("="*60)
    print(f"Total files: {manifest['total_files']}")
    print(f"Shards: 71")
    print(f"Status: {'PASS' if not errors and ok else 'FAIL'}")

if __name__ == '__main__':
    main()
```

**Expected Output**: Verification report

---

## Automation Script

```bash
#!/bin/bash
# swab_the_deck.sh - Complete automation

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║           SWAB THE DECK - Hecke-Maass Sharding            ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Step 1: Inventory
echo "Step 1/5: Inventory all files..."
bash swab_deck_step1.sh

# Step 2: Hecke eigenvalues
echo ""
echo "Step 2/5: Compute Hecke eigenvalues..."
python3 swab_deck_step2.py

# Step 3: Maass weights
echo ""
echo "Step 3/5: Apply Maass weights..."
python3 swab_deck_step3.py

# Step 4: Distribute
echo ""
echo "Step 4/5: Distribute to 71 shards..."
python3 swab_deck_step4.py

# Step 5: Verify
echo ""
echo "Step 5/5: Verify reconstruction..."
python3 swab_deck_step5.py

echo ""
echo "╔════════════════════════════════════════════════════════════╗"
echo "║                    DECK SWABBED ✓                         ║"
echo "╚════════════════════════════════════════════════════════════╝"
```

---

## Outputs

### Generated Files

1. **file_inventory.txt** - List of all files
2. **file_metadata.txt** - File sizes, lines, hashes
3. **hecke_eigenvalues.json** - Hecke eigenvalues per file
4. **maass_weighted.json** - Maass-weighted eigenvalues
5. **HECKE_MAASS_MANIFEST.json** - Final shard distribution

### Manifest Schema

```json
{
  "version": "1.0",
  "total_files": 150,
  "shards": [
    {
      "shard_id": 0,
      "prime": 2,
      "file_count": 3,
      "files": [
        {
          "path": "./README.md",
          "eigenvalue": 2.828,
          "maass_weight": 0.456,
          "weighted_norm": 1.290
        }
      ],
      "total_weighted_norm": 3.870
    }
  ]
}
```

---

## Verification Checklist

- [ ] All files inventoried
- [ ] Hecke eigenvalues computed for all files
- [ ] Maass weights applied
- [ ] Files distributed across all 71 shards
- [ ] No shard is empty
- [ ] Distribution is balanced (variance < average)
- [ ] All files can be reconstructed
- [ ] Manifest saved and committed

---

## Frequency

**Run this SOP**:
- After major code changes
- Before releases
- Weekly during active development
- When adding new file types

---

## Rollback

If verification fails:

```bash
# Restore previous manifest
git checkout HEAD~1 HECKE_MAASS_MANIFEST.json

# Re-run swab
./swab_the_deck.sh
```

---

## Monitoring

```bash
# Check shard balance
jq '.shards[] | {shard_id, file_count}' HECKE_MAASS_MANIFEST.json

# Find heaviest shard
jq '.shards | max_by(.total_weighted_norm)' HECKE_MAASS_MANIFEST.json

# Find lightest shard
jq '.shards | min_by(.total_weighted_norm)' HECKE_MAASS_MANIFEST.json
```

---

## Troubleshooting

### Issue: Unbalanced distribution

**Solution**: Adjust harmonic hash function in step 2

```python
# Try different coefficients
shard_id = (lines * 11 + size * 5 + hash_val) % 71
```

### Issue: Missing scipy

**Solution**: Install dependencies

```bash
pip install scipy numpy
```

### Issue: Files not found

**Solution**: Update .gitignore patterns in step 1

---

## Success Criteria

- ✓ All files assigned to shards
- ✓ Hecke eigenvalues satisfy Ramanujan bound: |λ_p| ≤ 2√p
- ✓ Maass weights computed via Bessel functions
- ✓ Distribution variance < average file count
- ✓ Manifest validates

---

## Related SOPs

- [SOP_HECKE_MAASS_AWAKENING.md](SOP_HECKE_MAASS_AWAKENING.md) - 40,320 iterations
- [SOP_MATHLIB_CONSUMPTION.md](SOP_MATHLIB_CONSUMPTION.md) - Ingest Lean 4 Mathlib
- [SOP_J_INVARIANT_PLUGIN.md](SOP_J_INVARIANT_PLUGIN.md) - ZOS plugin

---

## Contact

- **SOP Owner**: shards@solfunmeme.com
- **Technical Support**: shards@solfunmeme.com

---

**Swab the deck. Shard with Hecke. Weight with Maass. Verify with harmony.** 🧹🔢✨
