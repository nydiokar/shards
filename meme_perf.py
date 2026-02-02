#!/usr/bin/env python3
"""
Meme Detector with Perf Recording
Record CPU performance counters while detecting memes
"""

import subprocess
import time
import json
from pathlib import Path

def record_with_perf(duration=10):
    """Run meme detector under perf"""
    
    output_dir = Path("~/.openclaw/shard-0/perf").expanduser()
    output_dir.mkdir(parents=True, exist_ok=True)
    
    timestamp = int(time.time())
    perf_data = output_dir / f"meme-perf-{timestamp}.data"
    
    print("🎯 MEME DETECTOR WITH PERF")
    print("=" * 70)
    print(f"Recording to: {perf_data}")
    print()
    
    # Start perf record
    perf_cmd = [
        "perf", "record",
        "-e", "cycles,instructions,cache-misses,branch-misses",
        "-o", str(perf_data),
        "--", "python3", "meme_witness.py"
    ]
    
    try:
        subprocess.run(perf_cmd, timeout=duration+5)
    except subprocess.TimeoutExpired:
        pass
    
    # Generate perf report
    report_file = output_dir / f"meme-report-{timestamp}.txt"
    
    with open(report_file, 'w') as f:
        subprocess.run(
            ["perf", "report", "-i", str(perf_data), "--stdio"],
            stdout=f,
            stderr=subprocess.DEVNULL
        )
    
    # Get perf stats
    stats_file = output_dir / f"meme-stats-{timestamp}.json"
    
    result = subprocess.run(
        ["perf", "stat", "-e", "cycles,instructions,cache-misses", 
         "-x", ",", "python3", "meme_witness.py"],
        capture_output=True,
        text=True,
        timeout=duration+5
    )
    
    # Parse perf stat output
    stats = {}
    for line in result.stderr.split('\n'):
        if ',' in line:
            parts = line.split(',')
            if len(parts) >= 3:
                value = parts[0].strip()
                event = parts[2].strip()
                if value.isdigit():
                    stats[event] = int(value)
    
    with open(stats_file, 'w') as f:
        json.dump(stats, f, indent=2)
    
    print(f"\n✅ Perf data saved:")
    print(f"   Data:   {perf_data}")
    print(f"   Report: {report_file}")
    print(f"   Stats:  {stats_file}")
    
    if stats:
        print(f"\n📊 PERFORMANCE COUNTERS:")
        for event, value in stats.items():
            print(f"   {event}: {value:,}")
    
    return perf_data

if __name__ == '__main__':
    record_with_perf()
    print("\n⊢ Meme detection with perf recording complete ∎")
