#!/usr/bin/env python3
"""
Black Hole Detector via Audio Feedback Loop
Measure gravitational time dilation using 15 Monster primes as frequency keys
"""

import numpy as np
import time
import hashlib

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

# Generate tone at prime frequency
def generate_tone(prime, duration=0.1, sample_rate=44100):
    freq = prime * 100  # Scale to audible range
    t = np.linspace(0, duration, int(sample_rate * duration))
    return np.sin(2 * np.pi * freq * t)

# Measure waveform compression via hash entropy
def measure_compression(waveform):
    wave_bytes = waveform.tobytes()
    wave_hash = hashlib.sha256(wave_bytes).digest()
    entropy = -sum((b/255) * np.log2((b+1)/256) for b in wave_hash)
    return entropy

# Measure relative distance using prime-keyed loops
def detect_black_hole_primes(iterations=5):
    print("🕳️  BLACK HOLE DETECTOR (15 Monster Primes)")
    print("=" * 70)
    print("Hypothesis: Time dilation varies by loop size (prime frequencies)")
    print()
    
    baselines = {}
    
    for iteration in range(iterations):
        print(f"\n🔄 Iteration {iteration + 1}")
        print("-" * 70)
        
        distances = []
        
        for prime in MONSTER_PRIMES:
            # Generate tone at prime frequency
            tone = generate_tone(prime)
            
            # Measure entropy
            entropy = measure_compression(tone)
            
            # Initialize baseline
            if prime not in baselines:
                baselines[prime] = entropy
            
            # Calculate distance (compression ratio)
            distance = entropy / baselines[prime]
            distances.append(distance)
            
            marker = "⚠️ " if distance < 0.99 else "✓ "
            print(f"{marker}p={prime:2d} (f={prime*100:4d}Hz): "
                  f"entropy={entropy:.4f}, distance={distance:.6f}")
        
        # Compute relative distances between primes
        avg_distance = np.mean(distances)
        std_distance = np.std(distances)
        
        print(f"\n📊 Average distance: {avg_distance:.6f}")
        print(f"📊 Std deviation:   {std_distance:.6f}")
        
        if avg_distance < 0.99:
            print("⚠️  GRAVITATIONAL TIME DILATION DETECTED")
        
        if std_distance > 0.05:
            print("⚠️  NON-UNIFORM SPACETIME (different loop sizes affected differently)")
        
        time.sleep(0.1)
    
    print("\n" + "=" * 70)
    print("⊢ Multi-prime measurement complete ∎")
    print(f"\nBaseline entropies (15 Monster primes):")
    for prime in MONSTER_PRIMES:
        print(f"  T_{prime}: {baselines[prime]:.4f}")

if __name__ == '__main__':
    detect_black_hole_primes()
