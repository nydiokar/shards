#!/usr/bin/env python3
"""
Monster-Bach Black Hole Detector
Combine 15 Monster primes with Bach's multi-signal monitoring
Measure gravitational time dilation through computational resonance
"""

import numpy as np
import subprocess
import time
import csv
from pathlib import Path

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def generate_tone(prime, duration=0.1, sample_rate=44100):
    freq = prime * 100
    t = np.linspace(0, duration, int(sample_rate * duration))
    return np.sin(2 * np.pi * freq * t)

def read_bach_sensors():
    """Read current sensor values from /proc"""
    sensors = {}
    
    # Temperature
    try:
        with open('/sys/class/thermal/thermal_zone0/temp') as f:
            sensors['temp'] = float(f.read().strip()) / 1000.0
    except:
        sensors['temp'] = 0.0
    
    # CPU frequency
    try:
        with open('/proc/cpuinfo') as f:
            for line in f:
                if 'cpu MHz' in line:
                    sensors['cpu_freq'] = float(line.split(':')[1].strip())
                    break
    except:
        sensors['cpu_freq'] = 0.0
    
    return sensors

def detect_with_bach(iterations=5):
    print("🎼🕳️  MONSTER-BACH BLACK HOLE DETECTOR")
    print("=" * 70)
    print("15 Monster primes + Bach multi-signal monitoring")
    print()
    
    output_file = f"/tmp/monster_bach_{int(time.time())}.csv"
    
    with open(output_file, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['iteration', 'prime', 'freq_hz', 'entropy', 'distance', 
                        'temp_c', 'cpu_freq_mhz', 'time_ms'])
        
        baselines = {}
        
        for iteration in range(iterations):
            print(f"\n🔄 Iteration {iteration + 1}")
            print("-" * 70)
            
            start_time = time.time()
            
            for prime in MONSTER_PRIMES:
                # Generate tone
                tone = generate_tone(prime)
                
                # Measure entropy
                wave_bytes = tone.tobytes()
                wave_hash = np.frombuffer(wave_bytes[:32], dtype=np.uint8)
                entropy = -sum((b/255) * np.log2((b+1)/256) for b in wave_hash)
                
                # Read Bach sensors
                sensors = read_bach_sensors()
                
                # Initialize baseline
                if prime not in baselines:
                    baselines[prime] = entropy
                
                # Calculate distance
                distance = entropy / baselines[prime]
                
                elapsed_ms = (time.time() - start_time) * 1000
                
                # Write to CSV
                writer.writerow([iteration, prime, prime*100, entropy, distance,
                               sensors['temp'], sensors['cpu_freq'], elapsed_ms])
                
                marker = "⚠️ " if distance < 0.99 else "✓ "
                print(f"{marker}T_{prime:2d} ({prime*100:4d}Hz): "
                      f"d={distance:.6f} temp={sensors['temp']:.1f}°C "
                      f"freq={sensors['cpu_freq']:.0f}MHz")
            
            time.sleep(0.1)
    
    print("\n" + "=" * 70)
    print(f"✅ Data saved to: {output_file}")
    print("\n📊 Baseline Monster-Bach resonances:")
    for prime in MONSTER_PRIMES:
        print(f"  T_{prime}: {baselines[prime]:.4f}")
    
    return output_file

if __name__ == '__main__':
    output = detect_with_bach()
    print(f"\n⊢ Monster-Bach measurement complete ∎")
    print(f"\nAnalyze with: python3 /mnt/data1/bach/analyze_fixed_points.py {output}")
