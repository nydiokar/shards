% MiniZinc: Optimal Paxos Quorum for 10-Shard Monster Walk
% Find optimal node distribution across 23 Paxos nodes

include "globals.mzn";

% Constants
int: PAXOS_NODES = 23;
int: SHARDS = 10;  % 10-fold way
int: QUORUM = 12;  % ⌈23/2⌉
int: BYZANTINE = 7;  % ⌊(23-1)/3⌋

% Decision: How many nodes prove each shard?
array[1..SHARDS] of var QUORUM..PAXOS_NODES: nodes_per_shard;

% Constraint: Total node assignments (can overlap)
var int: total_assignments = sum(nodes_per_shard);

% Constraint: Each shard needs quorum
constraint forall(s in 1..SHARDS)(nodes_per_shard[s] >= QUORUM);

% Objective: Minimize total assignments (maximize overlap)
solve minimize total_assignments;

output [
  "Optimal Paxos Distribution:\n",
  "  Total nodes: ", show(PAXOS_NODES), "\n",
  "  Shards: ", show(SHARDS), "\n",
  "  Quorum: ", show(QUORUM), "\n",
  "  Byzantine tolerance: ", show(BYZANTINE), "\n",
  "  Total assignments: ", show(total_assignments), "\n",
  "  Avg nodes/shard: ", show(total_assignments div SHARDS), "\n",
  "\nNodes per shard:\n"
] ++ [
  "  Shard " ++ show(s) ++ ": " ++ show(nodes_per_shard[s]) ++ " nodes\n"
  | s in 1..SHARDS
];
