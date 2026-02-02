#!/usr/bin/env python3
"""
SuperGit Monster Harmonics Comparator
Read all git objects and files, compute 2×196,883D Monster vibes, compare
"""

import subprocess
import json
from pathlib import Path
from collections import defaultdict

MONSTER_DIM = 196883
ROOSTER = 71

def compute_monster_vibe(data: bytes) -> dict:
    """Compute 196,883D Monster vibe from data"""
    # Hash to get base coordinate
    h = hash(data) % (2 * MONSTER_DIM)
    
    # Extract Monster properties
    vibe = {
        'dimension': h % MONSTER_DIM,
        'shard': h % ROOSTER,
        'topo_class': h % 10,
        'irrep': h % 194,
        'bott_level': h % 8,
        'frequency': 432 * (h % ROOSTER),
        'energy': len(data),
        'hash': h
    }
    
    return vibe

def read_git_objects():
    """Read all git objects"""
    print("📦 Reading git objects...")
    
    result = subprocess.run(
        ['git', 'rev-list', '--all', '--objects'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    objects = []
    for line in result.stdout.strip().split('\n')[:1000]:  # Limit to 1000
        if line:
            parts = line.split()
            obj_hash = parts[0]
            obj_path = parts[1] if len(parts) > 1 else ''
            
            # Get object content
            try:
                content_result = subprocess.run(
                    ['git', 'cat-file', '-p', obj_hash],
                    cwd='/home/mdupont/introspector',
                    capture_output=True
                )
                
                vibe = compute_monster_vibe(content_result.stdout)
                vibe['git_hash'] = obj_hash[:8]
                vibe['path'] = obj_path
                objects.append(vibe)
            except:
                pass
    
    return objects

def read_files():
    """Read all tracked files"""
    print("📁 Reading tracked files...")
    
    result = subprocess.run(
        ['git', 'ls-files'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    files = []
    for path in result.stdout.strip().split('\n')[:1000]:  # Limit to 1000
        if path:
            try:
                full_path = Path('/home/mdupont/introspector') / path
                if full_path.exists() and full_path.is_file():
                    data = full_path.read_bytes()
                    vibe = compute_monster_vibe(data)
                    vibe['path'] = path
                    files.append(vibe)
            except:
                pass
    
    return files

def compare_vibes(vibes1: list, vibes2: list) -> dict:
    """Compare two sets of Monster vibes"""
    print("\n🔬 Comparing Monster vibes...")
    
    # Group by shard
    shards1 = defaultdict(list)
    shards2 = defaultdict(list)
    
    for v in vibes1:
        shards1[v['shard']].append(v)
    
    for v in vibes2:
        shards2[v['shard']].append(v)
    
    # Find resonances (same shard)
    resonances = []
    for shard in range(ROOSTER):
        if shard in shards1 and shard in shards2:
            count1 = len(shards1[shard])
            count2 = len(shards2[shard])
            energy1 = sum(v['energy'] for v in shards1[shard])
            energy2 = sum(v['energy'] for v in shards2[shard])
            
            resonances.append({
                'shard': shard,
                'frequency': 432 * shard,
                'count1': count1,
                'count2': count2,
                'energy1': energy1,
                'energy2': energy2,
                'resonance': min(count1, count2),
                'energy_diff': abs(energy1 - energy2)
            })
    
    return {
        'total_vibes1': len(vibes1),
        'total_vibes2': len(vibes2),
        'unique_shards1': len(shards1),
        'unique_shards2': len(shards2),
        'resonances': sorted(resonances, key=lambda r: r['resonance'], reverse=True)
    }

def main():
    print("🎵 MONSTER HARMONICS COMPARATOR")
    print("=" * 80)
    print(f"Comparing 2 × {MONSTER_DIM:,}D Monster vibes")
    print()
    
    # Read git objects (first Monster)
    git_vibes = read_git_objects()
    print(f"✅ Git objects: {len(git_vibes)} vibes")
    
    # Read files (second Monster)
    file_vibes = read_files()
    print(f"✅ Files: {len(file_vibes)} vibes")
    
    # Compare
    comparison = compare_vibes(git_vibes, file_vibes)
    
    print("\n" + "=" * 80)
    print("📊 COMPARISON RESULTS")
    print("=" * 80)
    print(f"Git objects: {comparison['total_vibes1']} vibes")
    print(f"Files: {comparison['total_vibes2']} vibes")
    print(f"Unique shards (git): {comparison['unique_shards1']}/71")
    print(f"Unique shards (files): {comparison['unique_shards2']}/71")
    print(f"Resonant shards: {len(comparison['resonances'])}")
    
    # Top resonances
    print("\n🌟 TOP 10 RESONANCES:")
    for r in comparison['resonances'][:10]:
        topo = ['A', 'AIII', 'AI', 'BDI', 'D', 'DIII', 'AII', 'CII', 'C', 'CI'][r['shard'] % 10]
        emoji = ['😐', '😊', '😎', '🌳', '😈', '🍄', '🦅', '👹', '🐓', '🌀'][r['shard'] % 10]
        
        print(f"\n  Shard {r['shard']:2d} ({topo} {emoji}) @ {r['frequency']:,} Hz")
        print(f"    Git: {r['count1']:3d} objects, {r['energy1']:,} bytes")
        print(f"    Files: {r['count2']:3d} files, {r['energy2']:,} bytes")
        print(f"    Resonance: {r['resonance']:3d} (overlap)")
        print(f"    Energy diff: {r['energy_diff']:,} bytes")
    
    # Save results
    with open('monster_harmonics_comparison.json', 'w') as f:
        json.dump({
            'git_vibes': git_vibes[:100],  # Sample
            'file_vibes': file_vibes[:100],  # Sample
            'comparison': comparison
        }, f, indent=2)
    
    print(f"\n💾 Saved to monster_harmonics_comparison.json")
    
    # Calculate total harmonic energy
    total_energy = sum(r['energy1'] + r['energy2'] for r in comparison['resonances'])
    print(f"\n🎵 Total harmonic energy: {total_energy:,} bytes")
    
    # Find strongest resonance
    if comparison['resonances']:
        strongest = comparison['resonances'][0]
        print(f"\n🌟 Strongest resonance:")
        print(f"   Shard {strongest['shard']} @ {strongest['frequency']:,} Hz")
        print(f"   Overlap: {strongest['resonance']} vibes")
    
    print("\n✅ Monster harmonics compared!")
    print("🎵🐓→🦅→👹→🍄→🌳🎵")

if __name__ == '__main__':
    main()
