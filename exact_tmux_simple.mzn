% EXACT tmux packing: 150x38 = 5700 chars (SIMPLIFIED)

int: W = 150;
int: H = 38;
int: TOTAL = 5700;

% 10 folds, allocate lines (not chars)
array[0..9] of var 1..H: lines;

% EXACT: use all 38 lines
constraint sum(f in 0..9)(lines[f]) = H;

% Bits per line (width * bits_per_char)
array[0..9] of int: bits_per_line = array1d(0..9, [
  900,  % 0: 150 * 6
  1200, % 1: 150 * 8
  1050, % 2: 150 * 7
  900,  % 3: 150 * 6
  1050, % 4: 150 * 7
  1200, % 5: 150 * 8
  900,  % 6: 150 * 6
  1200, % 7: 150 * 8
  450,  % 8: 150 * 3
  1200  % 9: 150 * 8
]);

% Weight
array[0..9] of int: weight = array1d(0..9, [5, 10, 8, 7, 6, 9, 7, 8, 6, 10]);

% Maximize
var int: total_bits = sum(f in 0..9)(
  lines[f] * bits_per_line[f] * weight[f]
);

solve maximize total_bits;

output [
  "🌀 EXACT TMUX PACKING (150x38)\n",
  "===============================\n",
  "FOLD │ EMOJI │ LINES │ CHARS │ BITS/L │ TOTAL_BITS\n",
  "─────┼───────┼───────┼───────┼────────┼───────────\n",
  "0.   │  ☕   │ " ++ show_int(5, lines[0]) ++ " │ " ++ show_int(5, lines[0] * W) ++ " │ " ++ show_int(6, bits_per_line[0]) ++ " │ " ++ show_int(9, lines[0] * bits_per_line[0] * weight[0]) ++ "\n",
  "1.   │  🕳️   │ " ++ show_int(5, lines[1]) ++ " │ " ++ show_int(5, lines[1] * W) ++ " │ " ++ show_int(6, bits_per_line[1]) ++ " │ " ++ show_int(9, lines[1] * bits_per_line[1] * weight[1]) ++ "\n",
  "2.   │  🪟   │ " ++ show_int(5, lines[2]) ++ " │ " ++ show_int(5, lines[2] * W) ++ " │ " ++ show_int(6, bits_per_line[2]) ++ " │ " ++ show_int(9, lines[2] * bits_per_line[2] * weight[2]) ++ "\n",
  "3.   │  👁️   │ " ++ show_int(5, lines[3]) ++ " │ " ++ show_int(5, lines[3] * W) ++ " │ " ++ show_int(6, bits_per_line[3]) ++ " │ " ++ show_int(9, lines[3] * bits_per_line[3] * weight[3]) ++ "\n",
  "4.   │  👹   │ " ++ show_int(5, lines[4]) ++ " │ " ++ show_int(5, lines[4] * W) ++ " │ " ++ show_int(6, bits_per_line[4]) ++ " │ " ++ show_int(9, lines[4] * bits_per_line[4] * weight[4]) ++ "\n",
  "5.   │  🦅   │ " ++ show_int(5, lines[5]) ++ " │ " ++ show_int(5, lines[5] * W) ++ " │ " ++ show_int(6, bits_per_line[5]) ++ " │ " ++ show_int(9, lines[5] * bits_per_line[5] * weight[5]) ++ "\n",
  "6.   │  🐓   │ " ++ show_int(5, lines[6]) ++ " │ " ++ show_int(5, lines[6] * W) ++ " │ " ++ show_int(6, bits_per_line[6]) ++ " │ " ++ show_int(9, lines[6] * bits_per_line[6] * weight[6]) ++ "\n",
  "7.   │  🔄   │ " ++ show_int(5, lines[7]) ++ " │ " ++ show_int(5, lines[7] * W) ++ " │ " ++ show_int(6, bits_per_line[7]) ++ " │ " ++ show_int(9, lines[7] * bits_per_line[7] * weight[7]) ++ "\n",
  "8.   │  🌀   │ " ++ show_int(5, lines[8]) ++ " │ " ++ show_int(5, lines[8] * W) ++ " │ " ++ show_int(6, bits_per_line[8]) ++ " │ " ++ show_int(9, lines[8] * bits_per_line[8] * weight[8]) ++ "\n",
  "9.   │  ⚡   │ " ++ show_int(5, lines[9]) ++ " │ " ++ show_int(5, lines[9] * W) ++ " │ " ++ show_int(6, bits_per_line[9]) ++ " │ " ++ show_int(9, lines[9] * bits_per_line[9] * weight[9]) ++ "\n",
  "─────┴───────┴───────┴───────┴────────┴───────────\n",
  "TOTAL: ", show(sum(f in 0..9)(lines[f])), "/", show(H), " lines ✓\n",
  "CHARS: ", show(sum(f in 0..9)(lines[f] * W)), "/", show(TOTAL), " ✓\n",
  "VALUE: ", show(total_bits), " weighted bits\n",
  "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
