% Optimal Muse-Emoji Assignment via Monster Shards
% Solve for beauty across 71 shards

include "globals.mzn";

% Data
int: n_muses = 9;
int: n_shards = 71;
array[1..n_muses] of int: muse_shards = [4, 18, 44, 33, 63, 43, 1, 67, 36];
array[1..n_muses] of int: muse_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23];
array[1..n_muses] of int: muse_layers = [0, 8, 16, 24, 32, 40, 48, 56, 64];

% Decision: assign each shard to a muse
array[0..n_shards-1] of var 1..n_muses: shard_to_muse;

% Constraint: muse's own shard must be assigned to itself
constraint forall(m in 1..n_muses)(
  shard_to_muse[muse_shards[m]] = m
);

% Beauty function
var int: beauty = sum(s in 0..n_shards-1)(
  let {
    int: m = shard_to_muse[s],
    int: dist = abs(s - muse_shards[m]),
    int: prime_bonus = muse_primes[m] * 10,
    int: layer_bonus = muse_layers[m],
    int: cusp_bonus = if s = 17 then 1000 else 0 endif,
  } in
    prime_bonus + layer_bonus - dist + cusp_bonus
);

% Maximize beauty
solve maximize beauty;

output [
  "Beauty: ", show(beauty), "\n",
  "Cusp (17) → Muse ", show(shard_to_muse[17]), "\n",
  "Terpsichore (1) → Muse ", show(shard_to_muse[1]), "\n",
  "\nShard assignments:\n"
] ++ [
  "Shard ", show_int(2, s), " → Muse ", show(shard_to_muse[s]), "\n"
  | s in 0..20
];
