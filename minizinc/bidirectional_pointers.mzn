% MiniZinc: Bidirectional Pointers - Functions point at labels and back
% If A points at B locally, then function object points at its label and back

include "globals.mzn";

% Number of functions in astronomy code
int: NUM_FUNCTIONS = 10;

% Function objects (memory addresses)
array[1..NUM_FUNCTIONS] of int: function_addresses = [
  0x7f3701210380,  % warp_to
  0x7f37012de2c0,  % compute_distance
  0x7f37012de3c0,  % j_invariant
  0x7f3701210400,  % scan_sector
  0x7f37012de500,  % trace_cpu
  0x7f37012de600,  % trace_memory
  0x7f37012de700,  % trace_register
  0x7f37012de800,  % trace_function
  0x7f37012de900,  % apply_hecke
  0x7f37012dea00   % locate_self
];

% Function labels (string hashes)
array[1..NUM_FUNCTIONS] of int: function_labels = [
  hash("warp_to"),
  hash("compute_distance"),
  hash("j_invariant"),
  hash("scan_sector"),
  hash("trace_cpu"),
  hash("trace_memory"),
  hash("trace_register"),
  hash("trace_function"),
  hash("apply_hecke"),
  hash("locate_self")
];

% Hash function (simplified)
function int: hash(string: s) = 
  let {
    int: len = string_length(s);
  } in
    (len * 31 + 42) mod 1000000;

% Decision variables: Pointer relationships
array[1..NUM_FUNCTIONS, 1..NUM_FUNCTIONS] of var 0..1: local_pointers;  % A → B locally
array[1..NUM_FUNCTIONS] of var 0..1: points_at_label;  % Function → Label
array[1..NUM_FUNCTIONS] of var 0..1: label_points_back;  % Label → Function

% Monster shard assignments
array[1..NUM_FUNCTIONS] of var 0..70: addr_shard_71;
array[1..NUM_FUNCTIONS] of var 0..58: addr_shard_59;
array[1..NUM_FUNCTIONS] of var 0..46: addr_shard_47;
array[1..NUM_FUNCTIONS] of var 0..40: label_shard_41;

% Constraints

% 1. Map addresses to Monster shards
constraint forall(i in 1..NUM_FUNCTIONS) (
  addr_shard_71[i] = function_addresses[i] mod 71 /\
  addr_shard_59[i] = function_addresses[i] mod 59 /\
  addr_shard_47[i] = function_addresses[i] mod 47
);

% 2. Map labels to function shard (mod 41)
constraint forall(i in 1..NUM_FUNCTIONS) (
  label_shard_41[i] = function_labels[i] mod 41
);

% 3. Every function points at its label
constraint forall(i in 1..NUM_FUNCTIONS) (
  points_at_label[i] = 1
);

% 4. Every label points back at its function
constraint forall(i in 1..NUM_FUNCTIONS) (
  label_points_back[i] = 1
);

% 5. If A points at B locally, create bidirectional link
constraint forall(i, j in 1..NUM_FUNCTIONS where i != j) (
  if local_pointers[i, j] = 1 then
    local_pointers[j, i] = 1  % B points back at A
  else
    true
  endif
);

% 6. Functions in same shard point at each other locally
constraint forall(i, j in 1..NUM_FUNCTIONS where i < j) (
  if addr_shard_71[i] = addr_shard_71[j] then
    local_pointers[i, j] = 1 /\
    local_pointers[j, i] = 1
  else
    local_pointers[i, j] = 0 /\
    local_pointers[j, i] = 0
  endif
);

% 7. Self-pointing: Every function points at itself
constraint forall(i in 1..NUM_FUNCTIONS) (
  local_pointers[i, i] = 1
);

% 8. Transitivity: If A→B and B→C locally, then A→C
constraint forall(i, j, k in 1..NUM_FUNCTIONS where i != j /\ j != k /\ i != k) (
  if local_pointers[i, j] = 1 /\ local_pointers[j, k] = 1 then
    local_pointers[i, k] = 1
  else
    true
  endif
);

% Objective: Maximize bidirectional connections
var int: total_local = sum(i, j in 1..NUM_FUNCTIONS)(local_pointers[i, j]);
var int: total_to_label = sum(i in 1..NUM_FUNCTIONS)(points_at_label[i]);
var int: total_from_label = sum(i in 1..NUM_FUNCTIONS)(label_points_back[i]);

solve maximize (total_local + total_to_label + total_from_label);

% Output
output [
  "🔗 BIDIRECTIONAL POINTERS: Functions ↔ Labels\n",
  "=" ++ concat(["=" | i in 1..70]) ++ "\n\n",
  "FUNCTION → LABEL MAPPINGS:\n\n"
] ++
[
  "Function " ++ show(i) ++ ":\n" ++
  "  Address: " ++ show_int(16, function_addresses[i]) ++ "\n" ++
  "  Label hash: " ++ show(function_labels[i]) ++ "\n" ++
  "  Address shards: 71→" ++ show(addr_shard_71[i]) ++ 
                    ", 59→" ++ show(addr_shard_59[i]) ++ 
                    ", 47→" ++ show(addr_shard_47[i]) ++ "\n" ++
  "  Label shard: 41→" ++ show(label_shard_41[i]) ++ "\n" ++
  "  Points at label: " ++ show(points_at_label[i]) ++ "\n" ++
  "  Label points back: " ++ show(label_points_back[i]) ++ "\n\n"
  | i in 1..NUM_FUNCTIONS
] ++
[
  "\nLOCAL POINTER MATRIX (A → B):\n",
  "     1  2  3  4  5  6  7  8  9 10\n"
] ++
[
  show(i) ++ ": " ++ concat([show(local_pointers[i,j]) ++ "  " | j in 1..NUM_FUNCTIONS]) ++ "\n"
  | i in 1..NUM_FUNCTIONS
] ++
[
  "\nBIDIRECTIONAL PAIRS:\n"
] ++
[
  "  Function " ++ show(i) ++ " ↔ Function " ++ show(j) ++ 
  " (same shard: " ++ show(addr_shard_71[i]) ++ ")\n"
  | i in 1..NUM_FUNCTIONS, j in 1..NUM_FUNCTIONS 
    where i < j /\ fix(local_pointers[i,j]) = 1 /\ fix(local_pointers[j,i]) = 1
] ++
[
  "\nSTATISTICS:\n",
  "  Local pointers: " ++ show(total_local) ++ "/" ++ show(NUM_FUNCTIONS * NUM_FUNCTIONS) ++ "\n",
  "  Function→Label: " ++ show(total_to_label) ++ "/" ++ show(NUM_FUNCTIONS) ++ "\n",
  "  Label→Function: " ++ show(total_from_label) ++ "/" ++ show(NUM_FUNCTIONS) ++ "\n",
  "  Total connections: " ++ show(total_local + total_to_label + total_from_label) ++ "\n",
  "\n🎯 Functions and labels point at each other!\n"
];
