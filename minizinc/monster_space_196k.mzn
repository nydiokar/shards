% MiniZinc: Optimal Packing of 194 Irreps into 71³ Hypercube
% Find optimal distribution of Monster symmetries

include "globals.mzn";

% Constants
int: MONSTER_DIM = 196883;
int: MONSTER_IRREPS = 194;
int: ROOSTER = 71;
int: HYPERCUBE = 357911;  % 71³
int: UMBRAL = 23;

% Decision: How many dimensions per irrep?
array[1..MONSTER_IRREPS] of var 1..MONSTER_DIM: dims_per_irrep;

% Constraint: Sum to Monster dimension
constraint sum(dims_per_irrep) = MONSTER_DIM;

% Constraint: Distribute evenly (minimize variance)
var int: max_dim = max(dims_per_irrep);
var int: min_dim = min(dims_per_irrep);
var int: variance = max_dim - min_dim;

% Objective: Minimize variance (even distribution)
solve minimize variance;

output [
  "Monster 196,883D Space Distribution:\n",
  "  Total irreps: ", show(MONSTER_IRREPS), "\n",
  "  Avg dims/irrep: ", show(MONSTER_DIM div MONSTER_IRREPS), "\n",
  "  Max dim: ", show(max_dim), "\n",
  "  Min dim: ", show(min_dim), "\n",
  "  Variance: ", show(variance), "\n",
  "  71³ capacity: ", show(HYPERCUBE), "\n",
  "  Overcapacity: ", show(HYPERCUBE - MONSTER_DIM), "×\n",
  "  Total symmetries (194×23): ", show(MONSTER_IRREPS * UMBRAL), "\n"
];
