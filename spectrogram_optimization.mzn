% Spectrogram optimization in MiniZinc
% Optimize FFT parameters for Monster group sharding

include "globals.mzn";

% Parameters
int: sample_rate = 16000;
int: duration_ms = 1000;
int: n_samples = sample_rate * duration_ms div 1000;

% Decision variables
var 128..2048: fft_size;
var 100..1000: window_size;
var 50..500: hop_size;

% Constraints

% 1. FFT size must be power of 2
constraint fft_size in {128, 256, 512, 1024, 2048};

% 2. Window size <= FFT size
constraint window_size <= fft_size;

% 3. Hop size <= window size (overlap)
constraint hop_size <= window_size;

% 4. Number of frames
var int: num_frames = (n_samples - window_size) div hop_size;

% 5. Shard to Monster group (mod 71)
var 0..70: shard = num_frames mod 71;

% 6. Bott class (audio = Real AI = 1)
var 0..9: bott = 1;

% 7. Optimal overlap (50-75%)
var float: overlap = 1.0 - (int2float(hop_size) / int2float(window_size));
constraint overlap >= 0.5;
constraint overlap <= 0.75;

% Objective: Maximize frames while keeping shard balanced
var int: cost = abs(shard - 35) * 10 + abs(num_frames - 100);

solve minimize cost;

output [
  "🎵 SPECTROGRAM OPTIMIZATION\n",
  "======================================================================\n\n",
  "FFT size: ", show(fft_size), "\n",
  "Window size: ", show(window_size), "\n",
  "Hop size: ", show(hop_size), "\n",
  "Overlap: ", show_float(2, 1, overlap * 100.0), "%\n\n",
  "Frames: ", show(num_frames), "\n",
  "Monster shard: ", show(shard), "/71\n",
  "Bott class: ", show(bott), " (Real AI)\n\n",
  "✅ Optimized for Monster group\n"
];
