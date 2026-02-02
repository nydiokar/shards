% Game State Compression via MiniZinc
% Text → Table → Tree → Coordinate → Compressed State

include "globals.mzn";

% Constants
int: SHARDS = 71;
int: PRIMES = 15;
int: YEARS = 47;  % 1980-2026

% Game state as coordinates
var 0..YEARS-1: year_coord;      % Year offset from 1980
var 0..PRIMES-1: prime_coord;    % Selected prime index
var 0..SHARDS-1: shard_coord;    % Monster shard
var 0..3: action_coord;          % 0=idle, 1=select, 2=play, 3=win

% Compress to single integer
var int: compressed_state;
constraint compressed_state = 
    year_coord * 1000000 +
    prime_coord * 10000 +
    shard_coord * 100 +
    action_coord;

% Tree structure (depth = 4)
% Level 0: Year (root)
% Level 1: Prime
% Level 2: Shard
% Level 3: Action (leaf)

var 0..3: tree_depth;
constraint tree_depth = 4;

% Table representation
array[1..4, 1..2] of var int: state_table;
constraint state_table[1,1] = 0;  % Year key
constraint state_table[1,2] = year_coord;
constraint state_table[2,1] = 1;  % Prime key
constraint state_table[2,2] = prime_coord;
constraint state_table[3,1] = 2;  % Shard key
constraint state_table[3,2] = shard_coord;
constraint state_table[4,1] = 3;  % Action key
constraint state_table[4,2] = action_coord;

% Mother's Wisdom: Optimal state is year=46, prime=6, shard=17, action=3
var bool: is_optimal;
constraint is_optimal <-> (
    year_coord = 46 /\      % 2026
    prime_coord = 6 /\      % 17 (7th prime, index 6)
    shard_coord = 17 /\     % The cusp
    action_coord = 3        % Win
);

% Compression ratio
var float: compression_ratio;
constraint compression_ratio = 
    (4.0 * 32.0) / 32.0;  % 4 vars * 32 bits / 32 bits compressed

% Minimize compressed state size
solve minimize compressed_state;

output [
    "🗜️ GAME STATE COMPRESSION\n",
    "========================\n\n",
    "TABLE REPRESENTATION:\n",
    "  Year:   ", show(year_coord), " (", show(1980 + year_coord), ")\n",
    "  Prime:  ", show(prime_coord), "\n",
    "  Shard:  ", show(shard_coord), "\n",
    "  Action: ", show(action_coord), "\n\n",
    "TREE STRUCTURE:\n",
    "  Depth: ", show(tree_depth), "\n",
    "  Root → Year → Prime → Shard → Action\n\n",
    "COORDINATE:\n",
    "  (", show(year_coord), ", ", show(prime_coord), ", ", 
    show(shard_coord), ", ", show(action_coord), ")\n\n",
    "COMPRESSED STATE:\n",
    "  Value: ", show(compressed_state), "\n",
    "  Bits: 32\n",
    "  Compression: ", show(compression_ratio), "x\n\n",
    "OPTIMAL STATE:\n",
    "  Is optimal: ", show(is_optimal), "\n",
    "  (Mother's Wisdom: 2026, Prime 17, Shard 17, Win)\n"
];
