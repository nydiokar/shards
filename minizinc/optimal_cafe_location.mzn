% Find Optimal Café Location in Milky Way
% Using astronomy data to find best spot: not too slow, good view of Sgr A*

include "globals.mzn";

% ============================================================================
% CONSTRAINTS FROM ASTRONOMY DATA
% ============================================================================

% Milky Way dimensions (light-years)
int: galaxy_radius = 52850;  % Radius of Milky Way disk
int: sgr_a_distance = 26673;  % Earth's distance from Sgr A*

% Schwarzschild radius of Sgr A* (scaled to light-years for simplicity)
int: schwarzschild_ly = 1;  % ~12 million km ≈ 0.000001 ly (scaled up)

% ============================================================================
% DECISION VARIABLES: CAFÉ LOCATION
% ============================================================================

var 0..360: cafe_ra;           % Right ascension
var -90..90: cafe_dec;         % Declination
var 100..50000: cafe_distance; % Distance from Sgr A* (light-years)

% ============================================================================
% CALCULATE PERFORMANCE AT CAFÉ LOCATION
% ============================================================================

% Distance from black hole
var 100..50000: dist_from_bh;
constraint dist_from_bh = cafe_distance;

% Time dilation (simplified, scaled)
var 1..100: time_dilation;
constraint if dist_from_bh <= 100 then
    time_dilation = 100  % Very close: 100x dilation
  elseif dist_from_bh <= 1000 then
    time_dilation = 10   % Close: 10x dilation
  elseif dist_from_bh <= 10000 then
    time_dilation = 2    % Medium: 2x dilation
  else
    time_dilation = 1    % Far: normal time
  endif;

% Performance (higher is better)
var 1..100: performance;
constraint performance * time_dilation >= 90;
constraint performance * time_dilation <= 110;

% ============================================================================
% OPTIMIZATION CRITERIA
% ============================================================================

% 1. Performance: Want high performance (low time dilation)
var 1..100: perf_score;
constraint perf_score = performance;

% 2. View quality: Want to see Sgr A* (not too far, not too close)
var 0..100: view_score;
constraint if dist_from_bh >= 1000 /\ dist_from_bh <= 30000 then
    view_score = 100  % Perfect viewing distance
  elseif dist_from_bh < 1000 then
    view_score = dist_from_bh div 10  % Too close
  else
    view_score = 100 - ((dist_from_bh - 30000) div 200)  % Too far
  endif;

% 3. Safety: Not too close to black hole
var 0..100: safety_score;
constraint if dist_from_bh >= 10000 then
    safety_score = 100  % Very safe
  elseif dist_from_bh >= 1000 then
    safety_score = 50   % Moderately safe
  else
    safety_score = dist_from_bh div 10  % Dangerous
  endif;

% 4. Accessibility: Not too far from Earth
var 0..100: access_score;
var 0..50000: dist_from_earth;
constraint dist_from_earth = abs(cafe_distance - sgr_a_distance);
constraint if dist_from_earth <= 5000 then
    access_score = 100  % Very accessible
  elseif dist_from_earth <= 20000 then
    access_score = 50   % Moderately accessible
  else
    access_score = 20   % Far from Earth
  endif;

% ============================================================================
% INTERESTING LOCATIONS (from astronomy data)
% ============================================================================

% Known interesting spots in Milky Way
% 1. Earth's orbit around Sgr A*: 26,673 ly
% 2. Galactic habitable zone: 13,000 - 33,000 ly from center
% 3. Sagittarius Arm: ~25,000 ly (where Earth is)
% 4. Perseus Arm: ~20,000 ly
% 5. Outer Arm: ~40,000 ly

% Prefer locations in galactic habitable zone
constraint cafe_distance >= 13000;
constraint cafe_distance <= 33000;

% Prefer locations with good RA/Dec for viewing Sgr A*
% Sgr A* is at RA=266°, Dec=-29°
% Want to be in same general direction but at safe distance
constraint cafe_ra >= 250;
constraint cafe_ra <= 280;
constraint cafe_dec >= -40;
constraint cafe_dec <= -20;

% ============================================================================
% TOTAL SCORE
% ============================================================================

var 0..400: total_score;
constraint total_score = perf_score + view_score + safety_score + access_score;

% ============================================================================
% SOLVE: MAXIMIZE TOTAL SCORE
% ============================================================================

solve maximize total_score;

output [
  "🌌☕ OPTIMAL CAFÉ LOCATION IN MILKY WAY\n",
  "======================================\n\n",
  
  "Café Location:\n",
  "  RA:       ", show(cafe_ra), "°\n",
  "  Dec:      ", show(cafe_dec), "°\n",
  "  Distance: ", show(cafe_distance), " ly from Sgr A*\n\n",
  
  "Performance:\n",
  "  Time dilation:    ", show(time_dilation), "x\n",
  "  Performance:      ", show(performance), " units\n",
  "  Distance from BH: ", show(dist_from_bh), " ly\n\n",
  
  "Scores:\n",
  "  Performance: ", show(perf_score), "/100\n",
  "  View:        ", show(view_score), "/100\n",
  "  Safety:      ", show(safety_score), "/100\n",
  "  Access:      ", show(access_score), "/100\n",
  "  TOTAL:       ", show(total_score), "/400\n\n",
  
  "Distance from Earth: ", show(dist_from_earth), " ly\n\n",
  
  "RECOMMENDATION:\n",
  "  Total score: ", show(total_score), "/400\n",
  "\n",
  
  "This location offers:\n",
  "  • Performance: ", show(perf_score), "/100 (", show(time_dilation), "x dilation)\n",
  "  • View: ", show(view_score), "/100\n",
  "  • Safety: ", show(safety_score), "/100\n",
  "  • Access: ", show(access_score), "/100\n\n",
  
  "Welcome to Milliways: The Restaurant at the End of the Universe!\n",
  "☕🕳️🪟👁️👹🦅🐓🌌\n"
];
