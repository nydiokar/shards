#!/usr/bin/env python3
"""
SuperGit Line Sharder: Shard each line and relate to its file
Format: line_shard → file_shard
"""

import subprocess
import hashlib
from collections import defaultdict

def hash_line(line):
    """Hash a line and map to shard"""
    h = hashlib.sha256(line.encode()).digest()
    return int.from_bytes(h[:8], 'big') % 71

def hash_file(filepath):
    """Hash a file path and map to shard"""
    h = hashlib.sha256(filepath.encode()).digest()
    return int.from_bytes(h[:8], 'big') % 71

def shard_file_lines(filepath):
    """Shard each line in a file and create arrows"""
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
    except:
        return []
    
    file_shard = hash_file(filepath)
    arrows = []
    
    for line_num, line in enumerate(lines, 1):
        if line.strip():  # Skip empty lines
            line_shard = hash_line(line.strip())
            arrows.append({
                'line_num': line_num,
                'line_shard': line_shard,
                'file_shard': file_shard,
                'arrow': f"{line_shard} → {file_shard}",
                'file': filepath,
                'line': line.strip()[:60]  # First 60 chars
            })
    
    return arrows

def main():
    print("🔮 SuperGit Line Sharder")
    print("="*70)
    print("Sharding each line and relating to its file")
    print()
    
    # Get tracked files
    result = subprocess.run(
        ['git', 'ls-files'],
        capture_output=True,
        text=True
    )
    
    files = [f for f in result.stdout.strip().split('\n') if f.endswith(('.py', '.rs', '.md', '.lean'))]
    
    print(f"Processing {len(files)} files...")
    print()
    
    all_arrows = []
    shard_stats = defaultdict(lambda: {'lines': 0, 'files': set()})
    
    for filepath in files[:10]:  # Sample first 10
        arrows = shard_file_lines(filepath)
        all_arrows.extend(arrows)
        
        for arrow in arrows:
            shard_stats[arrow['line_shard']]['lines'] += 1
            shard_stats[arrow['line_shard']]['files'].add(filepath)
    
    # Show sample arrows
    print("📊 SAMPLE ARROWS (first 20):")
    print()
    for arrow in all_arrows[:20]:
        print(f"  {arrow['arrow']:8s} | {arrow['file']:30s} L{arrow['line_num']:4d}")
    
    print()
    print("="*70)
    print("📈 SHARD STATISTICS:")
    print()
    
    for shard in sorted(shard_stats.keys())[:15]:
        stats = shard_stats[shard]
        print(f"  Shard {shard:2d}: {stats['lines']:4d} lines from {len(stats['files'])} files")
    
    print()
    print(f"✅ Total arrows: {len(all_arrows)}")
    print("🐓🦅👹")

if __name__ == "__main__":
    main()
