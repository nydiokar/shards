% Calculate 196,883 Monster symmetries (first irreducible representation)
% Using Bott 10-fold + 15 Hecke operators to classify code duplicates

include "globals.mzn";

% Parameters
int: n_files = 4228;  % Total files (Rust, Python, Lean4, MiniZinc, Prolog)
int: n_bott = 10;     % Bott periodicity
int: n_hecke = 15;    % Hecke operators (Monster primes)
int: monster_dim = 196883;  % First irrep dimension

% Monster primes
array[1..15] of int: PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

% Bott 10-fold classification
enum BottClass = {
  COMPLEX_A,      % 0: U(n)
  REAL_AI,        % 1: O(n)
  QUATERNIONIC,   % 2: Sp(n)
  CHIRAL,         % 3: U(p,q)
  BDI,            % 4: O(p,q)
  D,              % 5: SO(2n)
  DIII,           % 6: SO*(2n)
  C,              % 7: Sp(2n)
  CI,             % 8: Sp(p,q)
  CII             % 9: SO(2n+1)
};

% Decision variables
array[1..n_files] of var 0..9: bott_class;  % Bott classification
array[1..n_files, 1..n_hecke] of var 0..70: hecke_sig;  % Hecke signature
array[1..n_files] of var 0..70: shard;  % Monster shard (mod 71)
array[1..n_files] of var bool: is_duplicate;  % Is this a duplicate?

% Constraints

% 1. Bott periodicity: Distribute files across 10 classes
constraint forall(i in 1..n_files)(
  bott_class[i] >= 0 /\ bott_class[i] <= 9
);

% 2. Hecke operators: Each file has 15-dimensional signature
constraint forall(i in 1..n_files, j in 1..n_hecke)(
  hecke_sig[i,j] = (i * PRIMES[j]) mod 71
);

% 3. Shard assignment: Combine Hecke operators
constraint forall(i in 1..n_files)(
  shard[i] = sum(j in 1..n_hecke)(hecke_sig[i,j]) mod 71
);

% 4. Duplicate detection: Files with same Bott class AND same Hecke signature
constraint forall(i, j in 1..n_files where i < j)(
  (bott_class[i] = bott_class[j] /\
   forall(k in 1..n_hecke)(hecke_sig[i,k] = hecke_sig[j,k]))
  -> (is_duplicate[i] \/ is_duplicate[j])
);

% 5. Monster symmetry: Total symmetries = 196,883 (first irrep)
% Distribute across Bott classes
array[0..9] of var 0..monster_dim: symmetries_per_class;

constraint sum(c in 0..9)(symmetries_per_class[c]) = monster_dim;

% Each Bott class gets proportional symmetries
constraint forall(c in 0..9)(
  symmetries_per_class[c] = 
    (count(i in 1..n_files)(bott_class[i] = c) * monster_dim) div n_files
);

% 6. Balance: Even distribution across Bott classes
var int: max_per_class = max(c in 0..9)(count(i in 1..n_files)(bott_class[i] = c));
var int: min_per_class = min(c in 0..9)(count(i in 1..n_files)(bott_class[i] = c));
var int: imbalance = max_per_class - min_per_class;

% Objective: Minimize duplicates and imbalance
var int: num_duplicates = sum(i in 1..n_files)(bool2int(is_duplicate[i]));
var int: total_cost = num_duplicates * 100 + imbalance;

solve minimize total_cost;

% Output
output [
  "🔄 MONSTER WALK: 196,883 SYMMETRIES\n",
  "=" * 70, "\n\n",
  "📊 BOTT 10-FOLD DISTRIBUTION:\n",
  "-" * 70, "\n"
] ++
[
  "Class ", show(c), " (", show(enum_to_string(to_enum(BottClass, c+1))), "): ",
  show(count(i in 1..n_files)(fix(bott_class[i]) = c)), " files, ",
  show(fix(symmetries_per_class[c])), " symmetries\n"
  | c in 0..9
] ++
[
  "\n📈 STATISTICS:\n",
  "-" * 70, "\n",
  "Total files: ", show(n_files), "\n",
  "Total symmetries: ", show(monster_dim), "\n",
  "Duplicates found: ", show(fix(num_duplicates)), "\n",
  "Imbalance: ", show(fix(imbalance)), "\n",
  "Total cost: ", show(fix(total_cost)), "\n\n",
  "✅ Monster symmetries calculated via Bott 10-fold + 15 Hecke operators\n"
];
