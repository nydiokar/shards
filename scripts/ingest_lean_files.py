#!/usr/bin/env python3
"""Ingest all Lean files from .temp-find-lean.txt"""
import os
import json
from pathlib import Path
from collections import defaultdict

def is_lean_file(path):
    """Check if path is a Lean file"""
    return path.endswith('.lean')

def ingest_lean_file(path):
    """Read and parse a Lean file"""
    try:
        with open(path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        return {
            'path': path,
            'size': len(content),
            'lines': content.count('\n'),
            'has_theorem': 'theorem' in content,
            'has_def': 'def' in content,
            'has_inductive': 'inductive' in content,
            'has_structure': 'structure' in content,
            'has_class': 'class' in content,
            'content': content[:1000]  # First 1KB
        }
    except Exception as e:
        return {'path': path, 'error': str(e)}

def main():
    input_file = Path.home() / 'introspector' / '.temp-find-lean.txt'
    output_file = Path.home() / 'introspector' / 'lean_files_ingested.json'
    
    print(f"📖 Reading {input_file}...")
    
    with open(input_file, 'r') as f:
        all_paths = [line.strip() for line in f if line.strip()]
    
    print(f"Found {len(all_paths)} total paths")
    
    # Filter for .lean files
    lean_paths = [p for p in all_paths if is_lean_file(p)]
    print(f"Found {len(lean_paths)} Lean files")
    
    # Ingest each file
    results = []
    stats = defaultdict(int)
    
    for i, path in enumerate(lean_paths, 1):
        if i % 100 == 0:
            print(f"  Processing {i}/{len(lean_paths)}...")
        
        result = ingest_lean_file(path)
        results.append(result)
        
        if 'error' not in result:
            stats['success'] += 1
            stats['total_lines'] += result['lines']
            stats['total_size'] += result['size']
            if result['has_theorem']:
                stats['with_theorem'] += 1
            if result['has_def']:
                stats['with_def'] += 1
            if result['has_inductive']:
                stats['with_inductive'] += 1
        else:
            stats['errors'] += 1
    
    # Save results
    output = {
        'total_files': len(lean_paths),
        'stats': dict(stats),
        'files': results
    }
    
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n✅ Ingested {stats['success']} Lean files")
    print(f"   Total lines: {stats['total_lines']:,}")
    print(f"   Total size: {stats['total_size']:,} bytes")
    print(f"   With theorems: {stats['with_theorem']}")
    print(f"   With defs: {stats['with_def']}")
    print(f"   With inductives: {stats['with_inductive']}")
    print(f"   Errors: {stats['errors']}")
    print(f"\n💾 Saved to {output_file}")

if __name__ == '__main__':
    main()
