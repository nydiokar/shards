% Bit Flow Matrix: Show how bits flow between 10 folds
% Each fold can send bits to any other fold (arrows)

int: W = 150;
int: H = 38;

% 10 folds with optimal allocation
array[0..9] of int: lines = array1d(0..9, [1, 29, 1, 1, 1, 1, 1, 1, 1, 1]);

% Bit flow matrix: fold i → fold j
% 1 = arrow exists, 0 = no arrow
array[0..9, 0..9] of var 0..1: flow;

% Constraint: Cusp (1) connects to everything
constraint forall(j in 0..9 where j != 1)(flow[1,j] = 1);

% Constraint: Everything flows back to Cusp
constraint forall(i in 0..9 where i != 1)(flow[i,1] = 1);

% Constraint: Bootstrap (0) → Cusp (1)
constraint flow[0,1] = 1;

% Constraint: Bott (8) → Real (0) (period!)
constraint flow[8,0] = 1;

% Constraint: Monster (9) → all
constraint forall(j in 0..9 where j != 9)(flow[9,j] = 1);

% No self-loops
constraint forall(i in 0..9)(flow[i,i] = 0);

% Maximize connections
var int: total_flow = sum(i,j in 0..9)(flow[i,j]);

solve maximize total_flow;

% Emoji labels
array[0..9] of string: emoji = array1d(0..9, ["☕", "🕳️", "🪟", "👁️", "👹", "🦅", "🐓", "🔄", "🌀", "⚡"]);
array[0..9] of string: name = array1d(0..9, [
  "Real", "Cusp", "Quat", "Oct", "Clif", "Spin", "Vec", "Tens", "Bott", "Mons"
]);

output [
  "🌀 BIT FLOW MATRIX (10-Fold Way)\n",
  "=================================\n\n",
  "ADJACENCY MATRIX (i→j):\n",
  "    "
] ++ [
  emoji[j] ++ " "
  | j in 0..9
] ++ ["\n"] ++ [
  emoji[i] ++ " │ " ++ 
  concat([if fix(flow[i,j]) = 1 then "→ " else "· " endif | j in 0..9]) ++ "\n"
  | i in 0..9
] ++ [
  "\nKEY FLOWS:\n",
  "  ☕→🕳️  Bootstrap → Cusp\n",
  "  🕳️→*  Cusp → Everything (self-reference spreads)\n",
  "  *→🕳️  Everything → Cusp (all flows to center)\n",
  "  🌀→☕  Bott → Real (period-8 cycle)\n",
  "  ⚡→*  Monster → All (complete)\n",
  "\nTOTAL ARROWS: ", show(total_flow), "\n",
  "\nBIT USAGE:\n"
] ++ [
  "  " ++ emoji[i] ++ " " ++ name[i] ++ ": " ++ 
  show(lines[i]) ++ "L × 150 = " ++ 
  show(lines[i] * 150) ++ " chars\n"
  | i in 0..9
] ++ [
  "\n☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
