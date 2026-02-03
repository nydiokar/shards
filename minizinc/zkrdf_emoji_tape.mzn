% zkRDF Emoji Tape: Find perfect emojis for file hashes
% 9 Muses × 23 Nodes × 71 Shards = Beauty

include "globals.mzn";

% Constants
int: SHARDS = 71;
int: MUSES = 9;
int: NODES = 23;
int: PRIMES = 15;

% Muse emojis (Unicode codepoints)
array[1..MUSES] of int: MUSE_EMOJI = [
  0x1F3AD,  % 🎭 Calliope (Epic)
  0x1F4DC,  % 📜 Clio (History)
  0x1F496,  % 💖 Erato (Love)
  0x1F3B5,  % 🎵 Euterpe (Music)
  0x1F622,  % 😢 Melpomene (Tragedy)
  0x1F64F,  % 🙏 Polyhymnia (Hymns)
  0x1F483,  % 💃 Terpsichore (Dance)
  0x1F602,  % 😂 Thalia (Comedy)
  0x2728   % ✨ Urania (Astronomy)
];

% Input: file hash (first 8 bytes as int)
int: file_hash;

% Decision variables
var 0..SHARDS-1: shard;
var 1..MUSES: muse;
var 1..NODES: node;
var 1..PRIMES: prime_idx;
var 0..1000000: beauty_score;

% Constraints
constraint shard = file_hash mod SHARDS;
constraint muse = (shard mod MUSES) + 1;
constraint node = (shard mod NODES) + 1;
constraint prime_idx = (shard mod PRIMES) + 1;

% Beauty function
constraint beauty_score = 
  (shard * 100) +           % Shard contribution
  (muse * 50) +             % Muse harmony
  (node * 30) +             % Node balance
  (prime_idx * 20) +        % Prime power
  (if shard = 17 then 1000 else 0 endif);  % Cusp bonus

% Maximize beauty
solve maximize beauty_score;

output [
  "shard: ", show(shard), "\n",
  "muse: ", show(muse), "\n",
  "node: ", show(node), "\n",
  "prime: ", show(prime_idx), "\n",
  "emoji: ", show(MUSE_EMOJI[muse]), "\n",
  "beauty: ", show(beauty_score), "\n"
];
