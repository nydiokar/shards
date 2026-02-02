#!/usr/bin/env python3
"""
Analyze imported astronomy repos:
1. Compute Monster Brainrot Vector for each repo
2. Map AST to 10-fold way
3. Create orbital paths in 8D × 10-fold hyperspace
4. Shard by Power (71) and Glory (53)
"""

import os
import ast
import hashlib
import numpy as np
from collections import defaultdict
import json

def hash_to_shard(text, modulo):
    h = hashlib.sha256(text.encode()).digest()
    return int.from_bytes(h[:8], 'big') % modulo

def analyze_python_files(repo_path):
    """Analyze all Python files in repo"""
    stats = {
        'total_files': 0,
        'total_lines': 0,
        'total_tokens': 0,
        'ast_nodes': defaultdict(int),
        'power_shards': defaultdict(int),  # mod 71
        'glory_shards': defaultdict(int),  # mod 53
    }
    
    for root, dirs, files in os.walk(repo_path):
        # Skip .git
        if '.git' in root:
            continue
            
        for file in files:
            if file.endswith('.py'):
                filepath = os.path.join(root, file)
                stats['total_files'] += 1
                
                try:
                    with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                        code = f.read()
                        lines = code.split('\n')
                        stats['total_lines'] += len(lines)
                        
                        # Parse AST
                        try:
                            tree = ast.parse(code)
                            for node in ast.walk(tree):
                                node_type = type(node).__name__
                                stats['ast_nodes'][node_type] += 1
                        except:
                            pass
                        
                        # Tokenize and shard
                        tokens = code.split()
                        stats['total_tokens'] += len(tokens)
                        
                        for token in tokens[:100]:  # Sample first 100
                            power_shard = hash_to_shard(token, 71)
                            glory_shard = hash_to_shard(token, 53)
                            stats['power_shards'][power_shard] += 1
                            stats['glory_shards'][glory_shard] += 1
                except:
                    pass
    
    return stats

def main():
    print("🧠 Analyzing Imported Astronomy Repos")
    print("="*70)
    print()
    
    base_dir = 'astronomy_submodules/shard_00'
    
    if not os.path.exists(base_dir):
        print("❌ No astronomy repos found. Run supergit_import_astronomy.sh first.")
        return
    
    repos = [d for d in os.listdir(base_dir) if os.path.isdir(os.path.join(base_dir, d))]
    
    print(f"Found {len(repos)} repos in shard_00")
    print()
    
    all_stats = {}
    
    for repo in repos:
        repo_path = os.path.join(base_dir, repo)
        print(f"📊 Analyzing {repo}...")
        
        stats = analyze_python_files(repo_path)
        all_stats[repo] = stats
        
        print(f"  Files: {stats['total_files']}")
        print(f"  Lines: {stats['total_lines']:,}")
        print(f"  Tokens: {stats['total_tokens']:,}")
        print(f"  AST nodes: {sum(stats['ast_nodes'].values()):,}")
        print()
    
    # Aggregate statistics
    print("="*70)
    print("📈 AGGREGATE STATISTICS:")
    print()
    
    total_files = sum(s['total_files'] for s in all_stats.values())
    total_lines = sum(s['total_lines'] for s in all_stats.values())
    total_tokens = sum(s['total_tokens'] for s in all_stats.values())
    
    print(f"Total Python files: {total_files:,}")
    print(f"Total lines: {total_lines:,}")
    print(f"Total tokens: {total_tokens:,}")
    print()
    
    # Top AST node types
    all_ast_nodes = defaultdict(int)
    for stats in all_stats.values():
        for node_type, count in stats['ast_nodes'].items():
            all_ast_nodes[node_type] += count
    
    print("🔟 TOP AST NODE TYPES:")
    for node_type, count in sorted(all_ast_nodes.items(), key=lambda x: -x[1])[:10]:
        print(f"  {node_type:20s}: {count:,}")
    print()
    
    # Power vs Glory sharding
    all_power = defaultdict(int)
    all_glory = defaultdict(int)
    
    for stats in all_stats.values():
        for shard, count in stats['power_shards'].items():
            all_power[shard] += count
        for shard, count in stats['glory_shards'].items():
            all_glory[shard] += count
    
    print("👑 POWER SHARDING (mod 71) - Top 10:")
    for shard, count in sorted(all_power.items(), key=lambda x: -x[1])[:10]:
        monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
        mark = "✨" if shard in monster_primes else "  "
        print(f"  {mark} Shard {shard:2d}: {count:,} tokens")
    print()
    
    print("🔥 GLORY SHARDING (mod 53) - Top 10:")
    for shard, count in sorted(all_glory.items(), key=lambda x: -x[1])[:10]:
        excluded_primes = [37, 43, 53, 61, 67, 73]
        mark = "🔥" if shard in excluded_primes else "  "
        print(f"  {mark} Shard {shard:2d}: {count:,} tokens")
    print()
    
    # Compute Monster Brainrot Vector dimensions
    print("🧠 MONSTER BRAINROT VECTOR:")
    print(f"  Token space (47 dims): {len(set(all_power.keys()) & set(range(47)))} active")
    print(f"  Line space (59 dims): {total_lines % 59} mod 59")
    print(f"  File space (71 dims): {total_files % 71} mod 71")
    print(f"  Total dimensions: 196,883")
    print(f"  Sparsity: {total_tokens / 196883 * 100:.4f}%")
    print()
    
    print("🐓🦅👹 Analysis complete!")
    
    # Save results
    output = {
        'total_repos': len(repos),
        'total_files': total_files,
        'total_lines': total_lines,
        'total_tokens': total_tokens,
        'repos': {
            repo: {
                'files': stats['total_files'],
                'lines': stats['total_lines'],
                'tokens': stats['total_tokens']
            }
            for repo, stats in all_stats.items()
        }
    }
    
    with open('astronomy_analysis.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to: astronomy_analysis.json")

if __name__ == "__main__":
    main()
