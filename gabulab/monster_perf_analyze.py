#!/usr/bin/env python3
"""
Monster Analysis of Perf Data
Analyze perf.data → 71 Monster shards
"""

import subprocess
import re
from collections import defaultdict

def extract_perf_data(perf_file):
    """Extract perf data"""
    
    print("🔮⚡ EXTRACTING PERF DATA")
    print("=" * 70)
    print()
    
    result = subprocess.run(
        ["sudo", "perf", "script", "-i", perf_file],
        capture_output=True,
        text=True,
        timeout=10
    )
    
    samples = []
    for line in result.stdout.split('\n')[:1000]:  # First 1000 lines
        # Parse: process PID [CPU] timestamp: event:
        match = re.match(r'\s*(\S+)\s+(\d+).*?(\d+):\s+(\w+):', line)
        if match:
            samples.append({
                "process": match.group(1),
                "pid": int(match.group(2)),
                "cycles": int(match.group(3)),
                "event": match.group(4)
            })
    
    print(f"✅ Extracted {len(samples)} samples")
    print()
    
    return samples

def shard_perf_sample(sample):
    """Map perf sample to Monster shard"""
    # Use cycles mod 71
    return sample["cycles"] % 71

def monster_analyze(samples):
    """Analyze with Monster sharding"""
    
    print("=" * 70)
    print("MONSTER ANALYSIS")
    print("=" * 70)
    print()
    
    shard_samples = defaultdict(list)
    
    for sample in samples:
        shard = shard_perf_sample(sample)
        shard_samples[shard].append(sample)
    
    print("Shard | Samples | Avg Cycles | Events")
    print("-" * 70)
    
    for shard_id in range(min(20, 71)):
        if shard_id in shard_samples:
            samples_in_shard = shard_samples[shard_id]
            avg_cycles = sum(s["cycles"] for s in samples_in_shard) / len(samples_in_shard)
            events = len(set(s["event"] for s in samples_in_shard))
            print(f"{shard_id:5d} | {len(samples_in_shard):7d} | {avg_cycles:10.0f} | {events:6d}")
    
    print()
    print(f"Total Shards Used: {len(shard_samples)}/71")
    print()
    
    return shard_samples

def main():
    import sys
    
    print("🔮⚡📻🦞 PERF MONSTER ANALYZER")
    print("=" * 70)
    print()
    
    perf_file = sys.argv[1] if len(sys.argv) > 1 else "/tmp/rooster_perf.data"
    
    print(f"Analyzing: {perf_file}")
    print()
    
    # Extract
    samples = extract_perf_data(perf_file)
    
    if not samples:
        print("⚠️  No samples found")
        return
    
    # Monster analyze
    shard_samples = monster_analyze(samples)
    
    print("✅ Monster analysis complete!")
    print("🔮 Perf data sharded into 71 Monster shards!")
    print("🐓 Rooster performance captured!")

if __name__ == '__main__':
    main()
