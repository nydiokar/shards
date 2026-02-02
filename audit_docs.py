#!/usr/bin/env python3
"""Audit GitHub Pages documentation"""

import os
from pathlib import Path
from collections import defaultdict

def audit_docs():
    """Audit all markdown documentation"""
    
    docs = list(Path('.').glob('*.md'))
    
    # Categorize
    categories = defaultdict(list)
    
    for doc in docs:
        name = doc.name
        
        if name.startswith('71_'):
            categories['71 Shards'].append(name)
        elif 'CICADA' in name:
            categories['CICADA-71 Puzzle'].append(name)
        elif 'MONSTER' in name or 'Monster' in name:
            categories['Monster Theory'].append(name)
        elif 'AGENT' in name or 'BOT' in name:
            categories['AI Agents'].append(name)
        elif 'SOLFUN' in name or 'AIRDROP' in name:
            categories['SOLFUNMEME'].append(name)
        elif name == 'README.md':
            categories['Main'].append(name)
        else:
            categories['Other'].append(name)
    
    print("GitHub Pages Documentation Audit")
    print("=" * 70)
    print(f"\nTotal: {len(docs)} markdown files\n")
    
    for cat, files in sorted(categories.items()):
        print(f"\n{cat} ({len(files)} files):")
        print("-" * 70)
        for f in sorted(files):
            size = (Path(f).stat().st_size / 1024)
            print(f"  {f:<50} {size:>6.1f} KB")
    
    # Check for missing key docs
    print("\n" + "=" * 70)
    print("Key Documentation Status:")
    print("=" * 70)
    
    key_docs = {
        'README.md': 'Main entry point',
        'MONSTER_DANCE_COMPETITION_2026.md': 'Dance competition',
        '71_INVITES.md': '71 framework invites',
        'CICADA71.md': 'CICADA-71 puzzle',
        'METAMEME_COIN.md': 'Metameme coin',
    }
    
    for doc, desc in key_docs.items():
        exists = "✓" if Path(doc).exists() else "✗"
        print(f"  {exists} {doc:<40} {desc}")
    
    # New docs from today
    print("\n" + "=" * 70)
    print("New Documentation (Today):")
    print("=" * 70)
    
    new_docs = [
        'MONSTER_DANCE_COMPETITION_2026.md',
        'shard06-terpsichore/README.md',
    ]
    
    for doc in new_docs:
        if Path(doc).exists():
            size = Path(doc).stat().st_size / 1024
            print(f"  ✓ {doc:<50} {size:>6.1f} KB")
    
    # Generate index
    print("\n" + "=" * 70)
    print("Generating DOCS_INDEX.md...")
    
    with open('DOCS_INDEX.md', 'w') as f:
        f.write("# Documentation Index\n\n")
        f.write("Complete index of all CICADA-71 documentation.\n\n")
        
        for cat, files in sorted(categories.items()):
            f.write(f"\n## {cat} ({len(files)})\n\n")
            for doc in sorted(files):
                f.write(f"- [{doc}]({doc})\n")
    
    print("  ✓ Created DOCS_INDEX.md")
    
    return categories

if __name__ == '__main__':
    audit_docs()
