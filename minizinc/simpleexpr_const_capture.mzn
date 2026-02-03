% SimpleExpr Constants → Monster Group Elements
% Capture const values and map to Monster representation

include "globals.mzn";

% Monster group order (first 6 digits)
int: MONSTER_ORDER = 808017;

% 71 crown primes (shards)
array[1..15] of int: hecke_primes = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71];

% SimpleExpr const has: Name × List[Level]
% We capture these as Monster group elements

% Example constants from Lean4
set of int: CONST_IDS = 1..10;
array[CONST_IDS] of string: const_names = [
  "Nat", "Bool", "List", "Option", "Eq", 
  "And", "Or", "Not", "Exists", "Forall"
];

% Map each constant to a Hecke operator (mod 15)
array[CONST_IDS] of var 1..15: const_to_hecke;

% Map each constant to a shard (mod 71)
array[CONST_IDS] of var 1..71: const_to_shard;

% Constraint: shard = (hecke_prime * fold) mod 71
constraint forall(i in CONST_IDS)(
  const_to_shard[i] = (hecke_primes[const_to_hecke[i]] * 3) mod 71 + 1
);

% Each constant gets unique shard
constraint alldifferent(const_to_shard);

% Gödel encoding: hash const name to prime
function int: godel_hash(string: name) = 
  let {
    int: len = string_length(name);
  } in (len * 17 + 47) mod MONSTER_ORDER;

% Objective: maximize coverage of Monster group
var int: coverage = sum(i in CONST_IDS)(hecke_primes[const_to_hecke[i]]);

solve maximize coverage;

output [
  "SimpleExpr Constants → Monster Elements\n",
  "======================================\n\n"
] ++
[ "  \(const_names[i]): Shard \(const_to_shard[i]) (h\(hecke_primes[const_to_hecke[i]]))\n"
  | i in CONST_IDS
] ++
[
  "\nCoverage: \(coverage)\n",
  "Total Shards: 71\n"
];
