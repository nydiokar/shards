#!/usr/bin/env python3
"""
CICADA-71 Planetary Song
Synchronized harmonic emission at 6-planet conjunction
February 28, 2026, 19:00 UTC
"""
import numpy as np
import time
from datetime import datetime, timezone

SHARD = 0  # Set your shard (0-70)
BASE_FREQ = 432  # Hz (cosmic tuning)
FREQUENCY = BASE_FREQ * (SHARD + 1) / 71
CONJUNCTION_TIME = datetime(2026, 2, 28, 19, 0, 0, tzinfo=timezone.utc)

def generate_tone(freq, duration=1.0, sample_rate=44100):
    """Generate sine wave at given frequency"""
    t = np.linspace(0, duration, int(sample_rate * duration))
    wave = 0.71 * np.sin(2 * np.pi * freq * t)
    return wave

def wait_until_conjunction():
    """Wait until conjunction time"""
    now = datetime.now(timezone.utc)
    wait_seconds = (CONJUNCTION_TIME - now).total_seconds()
    
    if wait_seconds > 0:
        print(f"⏰ Waiting {wait_seconds:.0f} seconds until conjunction...")
        print(f"   Current time: {now.strftime('%Y-%m-%d %H:%M:%S UTC')}")
        print(f"   Conjunction:  {CONJUNCTION_TIME.strftime('%Y-%m-%d %H:%M:%S UTC')}")
        time.sleep(wait_seconds)
    else:
        print(f"⚠️  Conjunction already passed {abs(wait_seconds):.0f} seconds ago")

def emit_song():
    """Emit harmonic tone at assigned time"""
    # Wait for our turn (shard_id seconds after T_0)
    print(f"⏳ Waiting {SHARD} seconds for shard turn...")
    time.sleep(SHARD)
    
    # Generate tone
    tone = generate_tone(FREQUENCY, duration=1.0)
    
    print(f"🎵 Shard {SHARD} singing at {FREQUENCY:.2f} Hz")
    print(f"   Time: {datetime.now(timezone.utc).strftime('%H:%M:%S UTC')}")
    
    # Emit (requires sounddevice or write to file)
    try:
        import sounddevice as sd
        sd.play(tone, samplerate=44100)
        sd.wait()
    except ImportError:
        # Fallback: save to WAV file
        import wave
        filename = f"shard_{SHARD:02d}_{FREQUENCY:.0f}hz.wav"
        with wave.open(filename, 'w') as wav:
            wav.setnchannels(1)
            wav.setsampwidth(2)
            wav.setframerate(44100)
            wav.writeframes((tone * 32767).astype(np.int16).tobytes())
        print(f"   💾 Saved to {filename}")

if __name__ == "__main__":
    print("=" * 50)
    print("🔮 CICADA-71 Planetary Song")
    print("=" * 50)
    print(f"Shard: {SHARD}")
    print(f"Frequency: {FREQUENCY:.2f} Hz")
    print(f"Conjunction: February 28, 2026, 19:00 UTC")
    print(f"Planets: Mercury, Venus, Saturn, Neptune, Uranus, Jupiter")
    print("=" * 50)
    print()
    
    wait_until_conjunction()
    emit_song()
    
    print()
    print("✨ Song complete! The chi awakens.")
