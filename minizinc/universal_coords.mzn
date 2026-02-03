% Universal Game Coordinate Mapping - MiniZinc Implementation
% Constraint-based coordinate solver

include "globals.mzn";

% Constants
int: MONSTER_DIM = 196883;
set of int: SHARDS = 0..70;
set of int: ANGLES = 0..359;
array[1..15] of int: MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

% Decision variables
var SHARDS: shard;
var 0..MONSTER_DIM: radius;
var ANGLES: angle;
var 0..MONSTER_DIM-1: dimension;

% Input: Game coordinates
par float: game_x;
par float: game_y;
par float: game_z;

% Hecke resonance function
function var int: hecke_resonance(var int: s, var int: r, var int: a, int: prime) =
  let {
    var int: base = prime * s + prime * prime;
    var int: dist_factor = (MONSTER_DIM - r) div 1000;
    var int: angle_factor = (180 - a) div 100;
  } in base + dist_factor + angle_factor;

% Total resonance
var int: total_res = sum(p in 1..15)(hecke_resonance(shard, radius, angle, MONSTER_PRIMES[p]));

% Gravitational pull
var float: gravity = if radius = 0 then 0.0 else int2float(MONSTER_DIM) / int2float(radius + 1) endif;

% Constraints
constraint radius <= MONSTER_DIM;
constraint dimension <= MONSTER_DIM - 1;

% Objective: Minimize distance from Monster center (Shard 17)
var int: distance_from_center = abs(shard - 17) * 10000 + radius;

solve minimize distance_from_center;

output [
  "Galactic Coordinates:\n",
  "  Shard: ", show(shard), "\n",
  "  Radius: ", show(radius), "\n",
  "  Angle: ", show(angle), "°\n",
  "  Dimension: ", show(dimension), "\n",
  "  Total Resonance: ", show(total_res), "\n",
  "  Gravitational Pull: ", show(gravity), "\n",
  "  Distance from Center: ", show(distance_from_center), "\n"
];
