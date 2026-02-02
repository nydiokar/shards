#!/usr/bin/env bash
"""
SuperGit: Clone astronomy repos as submodules
Organize by Glory shards (mod 53)
Create git pack files for efficient storage
"""

set -e

echo "🌌 SuperGit: Cloning Astronomy Repos as Submodules"
echo "======================================================================"
echo ""

# Load glory sharding data
if [ ! -f glory_sharding.json ]; then
    echo "❌ glory_sharding.json not found. Run glory_sharding.py first."
    exit 1
fi

# Load astronomy map
if [ ! -f urania_astronomy_map.json ]; then
    echo "❌ urania_astronomy_map.json not found. Run urania_astronomy_map.py first."
    exit 1
fi

# Create submodules directory structure
echo "📁 Creating shard directories..."
mkdir -p astronomy_submodules

# Parse JSON and clone top repos (limit to 10 for demo)
python3 << 'PYTHON_SCRIPT'
import json
import subprocess
import os

# Load data
with open('urania_astronomy_map.json', 'r') as f:
    data = json.load(f)

with open('glory_sharding.json', 'r') as f:
    glory = json.load(f)

repos = data['repos']

# Sort by stars, take top 10
top_repos = sorted(repos, key=lambda x: x['stars'], reverse=True)[:10]

print(f"🚀 Cloning top {len(top_repos)} astronomy repos...")
print()

for i, repo in enumerate(top_repos, 1):
    full_name = repo['full_name']
    glory_shard = repo.get('glory_shard', 0)
    stars = repo['stars']
    
    # Create shard directory
    shard_dir = f"astronomy_submodules/shard_{glory_shard:02d}"
    os.makedirs(shard_dir, exist_ok=True)
    
    # Submodule path
    repo_name = full_name.split('/')[-1]
    submodule_path = f"{shard_dir}/{repo_name}"
    
    # Skip if already exists
    if os.path.exists(submodule_path):
        print(f"  ⏭️  [{i:2d}/10] {full_name} (already exists)")
        continue
    
    # Clone as submodule
    url = f"https://github.com/{full_name}.git"
    
    print(f"  📥 [{i:2d}/10] {full_name} ({stars}⭐) → shard {glory_shard}")
    
    try:
        # Use git submodule add
        result = subprocess.run(
            ['git', 'submodule', 'add', '--depth', '1', url, submodule_path],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            print(f"       ✅ Cloned to {submodule_path}")
        else:
            # Try regular clone if submodule fails
            result = subprocess.run(
                ['git', 'clone', '--depth', '1', url, submodule_path],
                capture_output=True,
                text=True,
                timeout=30
            )
            if result.returncode == 0:
                print(f"       ✅ Cloned (regular) to {submodule_path}")
            else:
                print(f"       ❌ Failed: {result.stderr[:100]}")
    except subprocess.TimeoutExpired:
        print(f"       ⏱️  Timeout")
    except Exception as e:
        print(f"       ❌ Error: {e}")

print()
print("📦 Creating git pack files...")

# Create pack files for each shard
for shard_num in range(53):
    shard_dir = f"astronomy_submodules/shard_{shard_num:02d}"
    if os.path.exists(shard_dir):
        print(f"  Packing shard {shard_num:02d}...")
        
        # Find all .git directories
        for root, dirs, files in os.walk(shard_dir):
            if '.git' in dirs:
                git_dir = os.path.join(root, '.git')
                try:
                    subprocess.run(
                        ['git', '-C', root, 'gc', '--aggressive'],
                        capture_output=True,
                        timeout=10
                    )
                except:
                    pass

print()
print("✅ SuperGit import complete!")
print()

# Statistics
total_size = 0
total_repos = 0
for root, dirs, files in os.walk('astronomy_submodules'):
    for file in files:
        filepath = os.path.join(root, file)
        try:
            total_size += os.path.getsize(filepath)
        except:
            pass
    if '.git' in root:
        total_repos += 1

print(f"📊 Statistics:")
print(f"  Total repos: {total_repos}")
print(f"  Total size: {total_size / 1024 / 1024:.2f} MB")
print()
print("🐓🦅👹 Astronomy repos imported to SuperGit!")

PYTHON_SCRIPT

echo ""
echo "💾 Updating .gitmodules..."
if [ -f .gitmodules ]; then
    echo "  ✅ .gitmodules exists"
    wc -l .gitmodules
else
    echo "  ℹ️  No submodules added (may have used regular clone)"
fi

echo ""
echo "🌌 SuperGit astronomy import complete!"
