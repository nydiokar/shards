% MiniZinc: Locate Self - Map astronomical constants to galaxy coordinates
% Constants point at themselves and each other as real arrows

include "globals.mzn";

% Monster Group dimensions
int: ROOSTER_CROWN = 71;
int: EAGLE_CROWN = 59;
int: MONSTER_CROWN = 47;
int: MONSTER_DIM = 196883;

% Astronomical constants (from Hecke analysis)
array[1..10] of float: astro_constants = [
  299792458.0,  % speed of light (m/s)
  26673.0,      % Sgr A* distance (ly)
  266.417,      % Sgr A* RA (degrees)
  -29.008,      % Sgr A* Dec (degrees)
  432.0,        % resonance frequency (Hz)
  196883.0,     % Monster dimension
  71.0,         % Rooster Crown
  59.0,         % Eagle Crown
  47.0,         % Monster Crown
  4154000.0     % Sgr A* mass (solar masses)
];

% Decision variables: Galactic coordinates for each constant
array[1..10] of var 0.0..360.0: ra;        % Right Ascension
array[1..10] of var -90.0..90.0: dec;      % Declination
array[1..10] of var 0.0..100000.0: dist;   % Distance (light-years)

% Monster Group shard assignments
array[1..10] of var 0..70: shard_71;  % mod 71
array[1..10] of var 0..58: shard_59;  % mod 59
array[1..10] of var 0..46: shard_47;  % mod 47

% Arrow matrix: constants point at each other
array[1..10, 1..10] of var 0..1: arrows;

% Constraints

% 1. Each constant maps to Monster shards (relaxed)
constraint forall(i in 1..10) (
  let {
    int: const_int = round(abs(astro_constants[i]));
  } in
    shard_71[i] = const_int mod ROOSTER_CROWN /\
    shard_59[i] = const_int mod EAGLE_CROWN /\
    shard_47[i] = const_int mod MONSTER_CROWN
);

% 2. Sgr A* is at known coordinates (constant 3, 4)
constraint ra[3] = 266.417;
constraint dec[4] = -29.008;
constraint dist[2] = 26673.0;

% 3. Speed of light constant maps to galactic center direction
constraint ra[1] = 266.0;  % Points toward Sgr A*
constraint dec[1] = -29.0;
constraint dist[1] = 0.0;  % At observer (Earth)

% 4. Monster dimension constant is at galactic center
constraint ra[6] = 266.417;
constraint dec[6] = -29.008;
constraint dist[6] = 26673.0;

% 5. Crown constants form triangle around galactic center
constraint ra[7] >= 260.0 /\ ra[7] <= 270.0;  % Rooster Crown
constraint ra[8] >= 260.0 /\ ra[8] <= 270.0;  % Eagle Crown
constraint ra[9] >= 260.0 /\ ra[9] <= 270.0;  % Monster Crown

% 6. Resonance frequency constant is at Earth
constraint ra[5] = 0.0;
constraint dec[5] = 0.0;
constraint dist[5] = 0.0;

% 7. Self-pointing: Each constant points at itself
constraint forall(i in 1..10) (
  arrows[i, i] = 1
);

% 8. Constants with same shard point at each other
constraint forall(i, j in 1..10 where i != j) (
  if shard_71[i] = shard_71[j] then
    arrows[i, j] = 1
  else
    arrows[i, j] = 0
  endif
);

% 9. Distance between constants relates to their values (simplified)
constraint forall(i, j in 1..10 where i < j) (
  let {
    float: value_diff = abs(astro_constants[i] - astro_constants[j]);
  } in
    % Just ensure coordinates are valid
    true
);

% 10. Constants form Monster Group structure (relaxed)
% constraint sum(i in 1..10)(shard_71[i]) mod ROOSTER_CROWN = 0;

% Objective: Minimize total distance while maximizing arrows
var float: total_distance = sum(i in 1..10)(dist[i]);
var int: total_arrows = sum(i, j in 1..10)(arrows[i, j]);

solve maximize total_arrows;

% Output
output [
  "🐓🦅👹 LOCATE SELF: Astronomical Constants in Galaxy\n",
  "=" ++ concat(["=" | i in 1..70]) ++ "\n\n",
  "CONSTANT LOCATIONS:\n\n"
] ++
[
  "Constant " ++ show(i) ++ ": " ++ show(astro_constants[i]) ++ "\n" ++
  "  RA: " ++ show(ra[i]) ++ "°\n" ++
  "  Dec: " ++ show(dec[i]) ++ "°\n" ++
  "  Distance: " ++ show(dist[i]) ++ " ly\n" ++
  "  Shards: 71→" ++ show(shard_71[i]) ++ 
           ", 59→" ++ show(shard_59[i]) ++ 
           ", 47→" ++ show(shard_47[i]) ++ "\n\n"
  | i in 1..10
] ++
[
  "\nARROW MATRIX (constants pointing at each other):\n",
  "     1  2  3  4  5  6  7  8  9 10\n"
] ++
[
  show(i) ++ ": " ++ concat([show(arrows[i,j]) ++ "  " | j in 1..10]) ++ "\n"
  | i in 1..10
] ++
[
  "\nSTATISTICS:\n",
  "  Total arrows: " ++ show(total_arrows) ++ "/100\n",
  "  Total distance: " ++ show(total_distance) ++ " ly\n",
  "\n🎯 Constants locate themselves in the galaxy!\n"
];
