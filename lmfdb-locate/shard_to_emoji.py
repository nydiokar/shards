#!/usr/bin/env python3
"""
Convert LMFDB files to emoji representation and assign to agents
"""

import json
from pathlib import Path
from collections import defaultdict

# Emoji mapping
EMOJI_MAP = {
    '.json': '📊',
    '.parquet': '🗄️',
    '.md': '📝',
    '.py': '🐍',
    '.rs': '🦀',
    '.pl': '🐪',
    '.sh': '🐚',
    '.yml': '⚙️',
    'elliptic': '🌀',
    'modular': '🔮',
    'lfunction': '📊',
    'maass': '🌊',
    'genus2': '〰️',
    'hmf': '🏛️',
    'siegel': '🎭',
    'artin': '⚡',
    'numberfield': '🔢',
    'galois': '👥',
}

def file_to_emoji(filepath):
    """Convert file path to emoji representation"""
    path = Path(filepath)
    emojis = []
    
    # Extension emoji
    ext = path.suffix
    if ext in EMOJI_MAP:
        emojis.append(EMOJI_MAP[ext])
    
    # Content emoji
    name_lower = path.name.lower()
    for keyword, emoji in EMOJI_MAP.items():
        if not keyword.startswith('.') and keyword in name_lower:
            emojis.append(emoji)
            break
    
    return ''.join(emojis) if emojis else '📄'

def shard_files():
    """Shard LMFDB files into 71 projects"""
    
    # Read all files
    with open('/tmp/lmfdb_all.txt', 'r') as f:
        files = [line.strip() for line in f if line.strip()]
    
    print(f"🔮⚡ Converting {len(files)} LMFDB files to emojis\n")
    
    # Shard into 71 buckets
    shards = defaultdict(list)
    for i, filepath in enumerate(files):
        shard_id = i % 71
        emoji = file_to_emoji(filepath)
        shards[shard_id].append({
            'path': filepath,
            'emoji': emoji,
            'name': Path(filepath).name
        })
    
    # Create output
    output = {
        'total_files': len(files),
        'num_shards': 71,
        'shards': {}
    }
    
    for shard_id in range(71):
        files_in_shard = shards.get(shard_id, [])
        output['shards'][f'shard_{shard_id}'] = {
            'id': shard_id,
            'count': len(files_in_shard),
            'files': files_in_shard,
            'agent': f'agent_{shard_id}',
            'emoji_summary': ''.join([f['emoji'] for f in files_in_shard[:10]])
        }
    
    # Save output
    with open('/tmp/lmfdb_emoji_shards.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"✅ Created 71 shards")
    print(f"📊 Average files per shard: {len(files) / 71:.1f}")
    print(f"\n📁 Output: /tmp/lmfdb_emoji_shards.json")
    
    # Print sample
    print(f"\n🔮 Sample shards:")
    for shard_id in [0, 7, 11, 42, 71-1]:
        shard = output['shards'][f'shard_{shard_id}']
        print(f"  Shard {shard_id:2d}: {shard['count']:2d} files {shard['emoji_summary']}")

if __name__ == '__main__':
    shard_files()
