% Meme Movement Prediction
% Generated from zkWitness

include "globals.mzn";

% Observed shards
array[1..94] of int: observed_shards = [0, 3, 21, 14, 61, 3, 35, 49, 62, 61, 6, 14, 19, 61, 0, 19, 62, 35, 14, 19, 62, 35, 61, 61, 20, 21, 0, 0, 19, 21, 61, 20, 21, 21, 21, 20, 4, 21, 19, 21, 6, 58, 62, 20, 0, 45, 6, 3, 49, 21, 0, 3, 45, 4, 20, 4, 6, 20, 20, 6, 58, 6, 62, 35, 45, 19, 35, 49, 3, 14, 20, 0, 48, 3, 45, 35, 48, 35, 0, 35, 20, 61, 4, 14, 35, 6, 49, 19, 35, 58, 48, 3, 6, 49];
array[1..94] of int: observed_primes = [71, 41, 3, 2, 29, 41, 5, 7, 19, 29, 11, 2, 23, 29, 71, 23, 19, 5, 2, 23, 19, 5, 29, 29, 13, 3, 71, 71, 23, 3, 29, 13, 3, 3, 3, 13, 31, 3, 23, 3, 11, 59, 19, 13, 71, 47, 11, 41, 7, 3, 71, 41, 47, 31, 13, 31, 11, 13, 13, 11, 59, 11, 19, 5, 47, 23, 5, 7, 41, 2, 13, 71, 17, 41, 47, 5, 17, 5, 71, 5, 13, 29, 31, 2, 5, 11, 7, 23, 5, 59, 17, 41, 11, 7];

% Predict next 5 positions
var 0..70: next_shard_1;
var 0..70: next_shard_2;
var 0..70: next_shard_3;
var 0..70: next_shard_4;
var 0..70: next_shard_5;

% Constraints: Follow observed pattern
constraint next_shard_1 != observed_shards[94];
constraint next_shard_2 != next_shard_1;
constraint next_shard_3 != next_shard_2;

% Prefer shards near cusp (17)
var int: distance_from_cusp = 
  abs(next_shard_1 - 17) + 
  abs(next_shard_2 - 17) + 
  abs(next_shard_3 - 17);

solve minimize distance_from_cusp;

output [
  "Next meme positions:\n",
  "  Shard ", show(next_shard_1), "\n",
  "  Shard ", show(next_shard_2), "\n",
  "  Shard ", show(next_shard_3), "\n",
  "  Shard ", show(next_shard_4), "\n",
  "  Shard ", show(next_shard_5), "\n"
];
