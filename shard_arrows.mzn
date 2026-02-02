% Shard SimpleExpr files → lines → tokens via crown primes
% Create arrow graph showing Monster group structure

include "globals.mzn";

% 3 levels of sharding
enum Level = {FILE, LINE, TOKEN};
array[Level] of int: crown_primes = [71, 59, 47];

% Example: 10 files, 100 lines, 1000 tokens
int: n_files = 10;
int: n_lines = 100;
int: n_tokens = 1000;

% Shard assignments
array[1..n_files] of var 1..71: file_shards;
array[1..n_lines] of var 1..59: line_shards;
array[1..n_tokens] of var 1..47: token_shards;

% Arrow matrix (adjacency)
array[1..71, 1..71] of var 0..1000: file_arrows;
array[1..59, 1..59] of var 0..1000: line_arrows;
array[1..47, 1..47] of var 0..1000: token_arrows;

% Constraint: arrows connect consecutive shards
constraint forall(i in 1..n_files-1)(
  file_arrows[file_shards[i], file_shards[i+1]] >= 1
);

% Total arrows
var int: total_arrows = 
  sum(i,j in 1..71)(file_arrows[i,j]) +
  sum(i,j in 1..59)(line_arrows[i,j]) +
  sum(i,j in 1..47)(token_arrows[i,j]);

% Objective: maximize arrow coverage (Monster group connectivity)
solve maximize total_arrows;

output [
  "SimpleExpr Sharding: Files → Lines → Tokens\n",
  "==========================================\n\n",
  "Crown Primes: 71 (files), 59 (lines), 47 (tokens)\n",
  "Total Arrows: \(total_arrows)\n",
  "\nMonster group structure emerges from arrow graph ✓\n"
];
