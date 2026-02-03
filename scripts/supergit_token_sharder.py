#!/usr/bin/env python3
"""
SuperGit Token Sharder: Three-level arrow system
- Token mod 47 (Monster Crown 👹)
- Line mod 59 (Eagle Crown 🦅)  
- File mod 71 (Rooster Crown 🐓)

Arrow chain: token@47 → line@59 → file@71
"""

import subprocess
import hashlib
import re
from collections import defaultdict

def hash_to_shard(text, modulo):
    """Hash text and map to shard"""
    h = hashlib.sha256(text.encode()).digest()
    return int.from_bytes(h[:8], 'big') % modulo

def tokenize(line):
    """Split line into tokens (words, symbols)"""
    return re.findall(r'\w+|[^\w\s]', line)

def shard_file_tokens(filepath):
    """Create three-level arrow system for file"""
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
    except:
        return []
    
    file_shard = hash_to_shard(filepath, 71)
    arrows = []
    
    for line_num, line in enumerate(lines, 1):
        if not line.strip():
            continue
            
        line_shard = hash_to_shard(line.strip(), 59)
        tokens = tokenize(line.strip())
        
        for token_pos, token in enumerate(tokens):
            if token.strip():
                token_shard = hash_to_shard(token, 47)
                
                arrows.append({
                    'token': token[:20],
                    'token_shard': token_shard,
                    'line_num': line_num,
                    'line_shard': line_shard,
                    'file': filepath,
                    'file_shard': file_shard,
                    'arrow': f"{token_shard}@47 → {line_shard}@59 → {file_shard}@71"
                })
    
    return arrows

def main():
    print("🐓🦅👹 SuperGit Token Sharder: Three Crowns")
    print("="*70)
    print("Token@47 → Line@59 → File@71")
    print()
    
    # Get tracked files
    result = subprocess.run(
        ['git', 'ls-files'],
        capture_output=True,
        text=True
    )
    
    files = [f for f in result.stdout.strip().split('\n') 
             if f.endswith(('.py', '.rs', '.md', '.lean'))][:5]  # First 5
    
    print(f"Processing {len(files)} files...")
    print()
    
    all_arrows = []
    crown_stats = {
        47: defaultdict(int),  # Monster Crown
        59: defaultdict(int),  # Eagle Crown
        71: defaultdict(int)   # Rooster Crown
    }
    
    for filepath in files:
        arrows = shard_file_tokens(filepath)
        all_arrows.extend(arrows)
        
        for arrow in arrows:
            crown_stats[47][arrow['token_shard']] += 1
            crown_stats[59][arrow['line_shard']] += 1
            crown_stats[71][arrow['file_shard']] += 1
    
    # Show sample arrows
    print("📊 SAMPLE ARROWS (first 25):")
    print()
    for arrow in all_arrows[:25]:
        token = arrow['token'][:15].ljust(15)
        print(f"  {token} | {arrow['arrow']}")
    
    print()
    print("="*70)
    print("👹 MONSTER CROWN (Token@47) - Top 10:")
    for shard, count in sorted(crown_stats[47].items(), key=lambda x: -x[1])[:10]:
        mark = "✨" if shard in [2,3,5,7,11,13,17,19,23,29,31,41,47] else "  "
        print(f"  {mark} Shard {shard:2d}: {count:4d} tokens")
    
    print()
    print("🦅 EAGLE CROWN (Line@59) - Top 10:")
    for shard, count in sorted(crown_stats[59].items(), key=lambda x: -x[1])[:10]:
        mark = "✨" if shard in [2,3,5,7,11,13,17,19,23,29,31,41,47,59] else "  "
        print(f"  {mark} Shard {shard:2d}: {count:4d} lines")
    
    print()
    print("🐓 ROOSTER CROWN (File@71) - All:")
    for shard, count in sorted(crown_stats[71].items()):
        mark = "✨" if shard in [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71] else "  "
        print(f"  {mark} Shard {shard:2d}: {count:4d} tokens")
    
    print()
    print(f"✅ Total arrows: {len(all_arrows)}")
    print("🐓🦅👹 Three Crowns Complete!")

if __name__ == "__main__":
    main()
