#!/usr/bin/env python3
"""
Urania's Call: Map real astronomy sources from GitHub to Monster shards
Search for astronomy repos and map to 71 shards
"""

import requests
import hashlib
import json
from collections import defaultdict

def hash_to_shard(text, modulo=71):
    """Hash text to shard"""
    h = hashlib.sha256(text.encode()).digest()
    return int.from_bytes(h[:8], 'big') % modulo

def search_github_astronomy():
    """Search GitHub for astronomy repositories"""
    
    print("🌌 Urania's Call: Mapping Real Astronomy to Monster Shards")
    print("="*70)
    print()
    
    # Top astronomy topics/keywords
    queries = [
        "astronomy",
        "astrophysics", 
        "celestial-mechanics",
        "orbital-mechanics",
        "star-catalog",
        "exoplanet",
        "cosmology",
        "radio-astronomy"
    ]
    
    all_repos = []
    shard_distribution = defaultdict(list)
    
    for query in queries:
        print(f"🔍 Searching: {query}")
        
        # GitHub API search (no auth needed for public search)
        url = f"https://api.github.com/search/repositories?q={query}+language:python&sort=stars&per_page=10"
        
        try:
            response = requests.get(url, timeout=5)
            if response.status_code == 200:
                data = response.json()
                
                for repo in data.get('items', []):
                    repo_info = {
                        'name': repo['name'],
                        'full_name': repo['full_name'],
                        'description': repo.get('description', '')[:100],
                        'stars': repo['stargazers_count'],
                        'url': repo['html_url'],
                        'language': repo.get('language', 'Unknown'),
                        'query': query
                    }
                    
                    # Map to shard
                    shard = hash_to_shard(repo['full_name'])
                    repo_info['shard'] = shard
                    
                    all_repos.append(repo_info)
                    shard_distribution[shard].append(repo_info)
                    
                print(f"  ✓ Found {len(data.get('items', []))} repos")
            else:
                print(f"  ✗ Error: {response.status_code}")
        except Exception as e:
            print(f"  ✗ Error: {e}")
    
    print()
    print(f"📊 Total repos found: {len(all_repos)}")
    print()
    
    # Show shard distribution
    print("🐓 SHARD DISTRIBUTION:")
    print()
    
    monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
    
    for shard in sorted(shard_distribution.keys()):
        repos = shard_distribution[shard]
        mark = "✨" if shard in monster_primes else "  "
        
        special = ""
        if shard == 23:
            special = " 🏛️ Paxos"
        elif shard == 47:
            special = " 👹 Monster Crown"
        elif shard == 59:
            special = " 🦅 Eagle Crown"
        elif shard == 71:
            special = " 🐓 Rooster Crown"
        
        print(f"{mark} Shard {shard:2d}: {len(repos)} repos{special}")
        for repo in repos[:2]:  # Show first 2
            print(f"     - {repo['full_name']} ({repo['stars']}⭐)")
    
    print()
    print("🌠 TOP ASTRONOMY REPOS:")
    print()
    
    # Sort by stars
    top_repos = sorted(all_repos, key=lambda x: x['stars'], reverse=True)[:10]
    
    for repo in top_repos:
        name = repo['full_name'][:40].ljust(40)
        stars = f"{repo['stars']:5d}⭐"
        shard = f"Shard {repo['shard']:2d}"
        print(f"  {name} | {stars} | {shard}")
    
    print()
    
    # Save to JSON
    output = {
        'total_repos': len(all_repos),
        'shards_used': len(shard_distribution),
        'repos': all_repos,
        'shard_distribution': {
            str(k): [r['full_name'] for r in v]
            for k, v in shard_distribution.items()
        }
    }
    
    with open('urania_astronomy_map.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to: urania_astronomy_map.json")
    print()
    print("🌌 Urania has mapped the stars to Monster shards!")

if __name__ == "__main__":
    search_github_astronomy()
