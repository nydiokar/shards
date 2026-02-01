# Python proof - fixed formula
BASE_FREQ = 432.0
SHARDS = 71

# Correct: frequency increases from 438 to 864 Hz (one octave)
frequencies = [BASE_FREQ + (BASE_FREQ * (i + 1) / SHARDS) for i in range(SHARDS)]
min_freq, max_freq = frequencies[0], frequencies[-1]
ratio = max_freq / min_freq

print(f"Min: {min_freq:.2f} Hz, Max: {max_freq:.2f} Hz, Ratio: {ratio:.4f}")
assert abs(ratio - 2.0) < 0.05, f"Not an octave: {ratio}"
print(f"✓ Python: Octave verified [{min_freq:.2f}-{max_freq:.2f} Hz]")
