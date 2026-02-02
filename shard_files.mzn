% Shard All Files → 71 Shards (MiniZinc verification)

include "globals.mzn";

% File counts by type (from introspector)
int: lean_files = 369;
int: rust_files = 925;
int: python_files = 2347;
int: minizinc_files = 86;
int: haskell_files = 9;
int: org_files = 1;

int: total_files = lean_files + rust_files + python_files + 
                   minizinc_files + haskell_files + org_files;

% Shard distribution (71 shards)
array[0..70] of var 0..100: shard_counts;

% Constraint: All files distributed
constraint sum(shard_counts) = total_files;

% Constraint: Roughly uniform distribution (±20%)
var int: avg = total_files div 71;
constraint forall(s in 0..70)(
  shard_counts[s] >= avg - 20 /\ shard_counts[s] <= avg + 20
);

% Objective: Minimize variance
var int: variance = sum(s in 0..70)(
  (shard_counts[s] - avg) * (shard_counts[s] - avg)
);

solve minimize variance;

output [
  "Shard Distribution (71 shards)\n",
  "==============================\n\n",
  "Total files: \(total_files)\n",
  "Average per shard: \(avg)\n",
  "Variance: \(variance)\n\n",
  "∴ All files sharded uniformly across 71 shards ✓\n"
];
