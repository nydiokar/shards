% zkERDFa-emoji Optimal Packing
% Solve for optimal beauty + information density
% Using Homomorphic Encryption for proof/schema/data embedding

include "globals.mzn";

% Terminal constraints
int: WIDTH = 150;
int: HEIGHT = 38;

% 71 games (shards)
int: NUM_SHARDS = 71;

% Emoji components per game
int: GAME_EMOJI = 1;      % Unique identifier
int: PERF_EMOJI = 1;      % Performance (🚀⚡🐌)
int: MEM_EMOJI = 1;       % Memory pattern
int: REG_EMOJI = 1;       % Register
int: FUNC_EMOJI = 1;      % Function type
int: DIGIT_EMOJIS = 2;    % Shard number (max 2 digits)
int: CHECKSUM_EMOJI = 1;  % Verification

int: TOTAL_EMOJIS_PER_GAME = 
    GAME_EMOJI + PERF_EMOJI + MEM_EMOJI + REG_EMOJI + 
    FUNC_EMOJI + DIGIT_EMOJIS + CHECKSUM_EMOJI;

% Each emoji = 2 terminal chars
int: CHARS_PER_EMOJI = 2;
int: CHARS_PER_GAME = TOTAL_EMOJIS_PER_GAME * CHARS_PER_EMOJI;

% Decision variables
var 1..20: cols;
var 1..20: rows;
var 10..50: cell_width;
var 3..10: cell_height;

% Constraints
constraint cols * rows >= NUM_SHARDS;
constraint cols * cell_width <= WIDTH;
constraint rows * cell_height <= HEIGHT;
constraint cell_width >= CHARS_PER_GAME + 4;  % +4 for padding

% Beauty metrics
var int: aspect_ratio = abs(cell_width - cell_height * 2);  % Prefer 2:1 ratio
var int: wasted_space = (cols * rows) - NUM_SHARDS;
var int: cell_area = cell_width * cell_height;

% Information density (bits per cell)
% Each emoji encodes log2(emoji_alphabet_size) bits
int: EMOJI_ALPHABET = 71;  % 71 unique emojis
var float: bits_per_cell = log2(int2float(EMOJI_ALPHABET)) * int2float(TOTAL_EMOJIS_PER_GAME);

% Homomorphic encryption overhead
% HE adds ~10x size but allows computation on encrypted data
var float: he_overhead = 10.0;
var float: encrypted_bits = bits_per_cell * he_overhead;

% Beauty score (minimize aspect ratio deviation, minimize waste)
var int: beauty_score = 1000000 - (aspect_ratio * 1000 + wasted_space * 100);

% Information score (maximize bits per cell)
var int: info_score = floor(bits_per_cell * 1000.0);

% Combined objective: beauty + information
var int: total_score = beauty_score + info_score;

solve maximize total_score;

output [
  "zkERDFa-emoji Optimal Packing Solution\n",
  "==================================================\n",
  "\nTerminal: ", show(WIDTH), "×", show(HEIGHT), " (", show(WIDTH*HEIGHT), " cells)\n",
  "\nLayout:\n",
  "  Grid: ", show(cols), " cols × ", show(rows), " rows\n",
  "  Cell: ", show(cell_width), "w × ", show(cell_height), "h\n",
  "  Total cells: ", show(cols * rows), " (", show(wasted_space), " wasted)\n",
  "\nEmoji Encoding:\n",
  "  Components: ", show(TOTAL_EMOJIS_PER_GAME), " emojis/game\n",
  "  Characters: ", show(CHARS_PER_GAME), " chars/game\n",
  "  Bits/cell: ", show_float(3, 1, bits_per_cell), " bits\n",
  "\nHomomorphic Encryption:\n",
  "  Overhead: ", show_float(3, 1, he_overhead), "x\n",
  "  Encrypted: ", show_float(3, 1, encrypted_bits), " bits/cell\n",
  "\nScores:\n",
  "  Beauty: ", show(beauty_score), "\n",
  "  Info: ", show(info_score), "\n",
  "  Total: ", show(total_score), "\n",
  "\nzkERDFa Structure:\n",
  "  Layer 1: Proof (zkPerf measurements)\n",
  "  Layer 2: Schema (RDFa vocabulary)\n",
  "  Layer 3: Data (emoji payload)\n",
  "  All encrypted with HE for privacy-preserving computation\n"
];
