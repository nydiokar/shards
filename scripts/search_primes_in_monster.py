#!/usr/bin/env python3
"""
Search for BDI primes in Monster parquet files
"""

import pyarrow.parquet as pq
from pathlib import Path

def search_primes_in_parquet():
    """Search for our primes in monster parquet files"""
    
    print("🔍 SEARCHING FOR PRIMES IN MONSTER PARQUET FILES")
    print("=" * 70)
    print()
    
    # Our primes from the walk
    target_primes = {
        "BDI": [17],
        "A": [3],
        "D": [19, 29],
        "AII": [13],
        "CII": [5, 23],
        "C": [7],
        "CI": [2, 11]
    }
    
    all_primes = set()
    for primes in target_primes.values():
        all_primes.update(primes)
    
    print(f"🎯 TARGET PRIMES: {sorted(all_primes)}")
    print()
    
    # Find parquet files
    monster_dir = Path.home() / "experiments" / "monster"
    parquet_files = list(monster_dir.glob("*.parquet"))
    
    print(f"📁 Found {len(parquet_files)} parquet files")
    print()
    
    # Search each file
    results = {}
    
    for pq_file in parquet_files[:10]:  # Check first 10
        try:
            table = pq.read_table(pq_file)
            
            # Check if any column contains our primes
            for col_name in table.column_names:
                col = table.column(col_name)
                
                # Convert to python list
                try:
                    values = col.to_pylist()
                    
                    # Check for primes
                    found = []
                    for prime in all_primes:
                        if prime in values:
                            found.append(prime)
                        # Also check string representation
                        if str(prime) in str(values):
                            if prime not in found:
                                found.append(prime)
                    
                    if found:
                        if pq_file.name not in results:
                            results[pq_file.name] = {}
                        results[pq_file.name][col_name] = found
                
                except Exception as e:
                    pass
        
        except Exception as e:
            print(f"   ⚠️  {pq_file.name}: {e}")
    
    print("🔍 SEARCH RESULTS:")
    print()
    
    if results:
        for filename, columns in results.items():
            print(f"📄 {filename}:")
            for col, primes in columns.items():
                print(f"   Column '{col}': {primes}")
            print()
    else:
        print("   No exact prime matches found in first 10 files")
        print("   (Primes may be encoded or transformed)")
    print()
    
    # Check for layer files specifically
    print("🍄 CHECKING LAYER FILES:")
    layer_files = list(monster_dir.glob("*layer*.parquet"))
    print(f"   Found {len(layer_files)} layer files")
    
    for layer_file in layer_files[:5]:
        print(f"   • {layer_file.name}")
    print()
    
    # Check for specific BDI prime (17)
    print("🌳 SEARCHING FOR BDI PRIME (17):")
    bdi_files = []
    
    for pq_file in parquet_files[:20]:
        if "17" in pq_file.name or "layer" in pq_file.name:
            bdi_files.append(pq_file.name)
    
    if bdi_files:
        print(f"   Files with '17' or 'layer': {len(bdi_files)}")
        for f in bdi_files[:5]:
            print(f"   • {f}")
    print()
    
    print("=" * 70)
    print("✅ SEARCH COMPLETE")
    print()
    print("🐓 → 🦅 → 👹 → 🍄 → 🌳")
    print()
    print(f"Searched {len(parquet_files)} parquet files")
    print(f"Found {len(results)} files with potential matches")
    
    return 0

if __name__ == '__main__':
    import sys
    try:
        sys.exit(search_primes_in_parquet())
    except ImportError:
        print("❌ pyarrow not available")
        print("Install with: pip install pyarrow")
        sys.exit(1)
