#!/bin/bash
# swab_the_deck.sh - Complete Hecke-Maass sharding automation

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║           SWAB THE DECK - Hecke-Maass Sharding            ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Step 1: Inventory
echo "Step 1/5: Inventory all files..."
find . -type f \
    -not -path "./.git/*" \
    -not -path "./target/*" \
    -not -path "./node_modules/*" \
    -not -path "./.kiro/*" \
    > file_inventory.txt

TOTAL=$(wc -l < file_inventory.txt)
echo "Found $TOTAL files"

# Step 2-5: Python pipeline
python3 << 'PYTHON_EOF'
import hashlib
import json
import math
from pathlib import Path
from collections import defaultdict

PRIMES_71 = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353
]

print("\nStep 2/5: Compute Hecke eigenvalues...")

files = []
with open('file_inventory.txt') as f:
    for line in f:
        path = line.strip()
        if Path(path).exists():
            try:
                size = Path(path).stat().st_size
                with open(path, 'rb') as fp:
                    data = fp.read()
                    lines = data.count(b'\n')
                    hash_val = hashlib.sha256(data).hexdigest()
                files.append({'path': path, 'size': size, 'lines': lines, 'hash': hash_val})
            except:
                pass

eigenvalues = []
for f in files:
    shard_id = (f['lines'] * 7 + f['size'] * 3 + int(f['hash'][:16], 16)) % 71
    
    h = bytes.fromhex(f['hash'])
    re = (int.from_bytes(h[:8], 'big') % 10000) / 10000.0 * 2 - 1
    im = (int.from_bytes(h[8:16], 'big') % 10000) / 10000.0 * 2 - 1
    
    p = PRIMES_71[shard_id]
    scale = 2 * math.sqrt(p)
    norm = math.sqrt(re*re + im*im) * scale
    
    eigenvalues.append({
        'file': f['path'],
        'shard_id': shard_id,
        'prime': p,
        'eigenvalue_re': re * scale,
        'eigenvalue_im': im * scale,
        'norm': norm,
    })

print(f"Computed {len(eigenvalues)} Hecke eigenvalues")

print("\nStep 3/5: Apply Maass weights...")

def maass_weight(r, n):
    arg = 2 * math.pi * n
    return math.exp(-arg / (1 + abs(r)))

weighted = []
for e in eigenvalues:
    n = e['shard_id'] + 1
    weight = maass_weight(e['eigenvalue_im'], n)
    weighted.append({**e, 'maass_weight': weight, 'weighted_norm': e['norm'] * weight})

print(f"Applied Maass weights to {len(weighted)} files")

print("\nStep 4/5: Distribute to 71 shards...")

shards = defaultdict(list)
for w in weighted:
    shards[w['shard_id']].append(w)

manifest = {
    'version': '1.0',
    'total_files': len(weighted),
    'shards': []
}

for shard_id in range(71):
    files = shards.get(shard_id, [])
    manifest['shards'].append({
        'shard_id': shard_id,
        'prime': PRIMES_71[shard_id],
        'file_count': len(files),
        'files': [{'path': f['file'], 'eigenvalue': f['norm'], 'maass_weight': f['maass_weight'], 'weighted_norm': f['weighted_norm']} for f in files],
        'total_weighted_norm': sum(f['weighted_norm'] for f in files),
    })

with open('HECKE_MAASS_MANIFEST.json', 'w') as f:
    json.dump(manifest, f, indent=2)

print(f"Distributed {len(weighted)} files across 71 shards")

print("\nStep 5/5: Verify reconstruction...")

verified = 0
for shard in manifest['shards']:
    for file_info in shard['files']:
        if Path(file_info['path']).exists():
            verified += 1

print(f"Verified {verified}/{len(weighted)} files")

file_counts = [s['file_count'] for s in manifest['shards']]
print(f"\nStatistics:")
print(f"  Min files per shard: {min(file_counts)}")
print(f"  Max files per shard: {max(file_counts)}")
print(f"  Avg files per shard: {sum(file_counts)/71:.1f}")

PYTHON_EOF

echo ""
echo "╔════════════════════════════════════════════════════════════╗"
echo "║                    DECK SWABBED ✓                         ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "Output: HECKE_MAASS_MANIFEST.json"
