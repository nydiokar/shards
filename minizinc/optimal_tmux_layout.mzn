% Optimal Information Packing for 150x38 tmux window
% Maximize information density while maintaining readability

% Terminal dimensions
int: width = 150;
int: height = 38;
int: total_cells = width * height;  % 5700 cells

% Information types to pack
enum InfoType = {HEADER, STATUS, CODE, OUTPUT, DOCS, METRICS, EMOJI};

% Character costs per info type (lower = more dense)
array[InfoType] of int: char_cost = [
  80,   % HEADER: Title line
  150,  % STATUS: Current state
  1000, % CODE: Source code
  500,  % OUTPUT: Command output
  800,  % DOCS: Documentation
  200,  % METRICS: Numbers/stats
  50    % EMOJI: Visual markers
];

% Information value per type (higher = more important)
array[InfoType] of int: info_value = [
  100,  % HEADER
  200,  % STATUS
  500,  % CODE
  300,  % OUTPUT
  150,  % DOCS
  400,  % METRICS
  50    % EMOJI
];

% Decision: how many chars of each type
array[InfoType] of var 0..total_cells: chars;

% Constraint: fit in terminal
constraint sum(i in InfoType)(chars[i]) <= total_cells;

% Constraint: minimum requirements
constraint chars[HEADER] >= 80;      % At least one header line
constraint chars[STATUS] >= 150;     % At least one status line
constraint chars[EMOJI] >= 50;       % Visual markers
constraint chars[METRICS] >= 200;    % Key numbers

% Constraint: readability (max 80 cols for code/docs)
constraint chars[CODE] <= 80 * 30;   % Max 30 lines of code
constraint chars[DOCS] <= 80 * 20;   % Max 20 lines of docs

% Maximize information value
var int: total_value = sum(i in InfoType)(
  (chars[i] div char_cost[i]) * info_value[i]
);

solve maximize total_value;

output [
  "🌀⚡ OPTIMAL TMUX LAYOUT (150x38 = 5700 cells)\n",
  "============================================\n\n",
  "HEADER:  ", show(chars[HEADER]), " chars (", 
    show(chars[HEADER] div width), " lines)\n",
  "STATUS:  ", show(chars[STATUS]), " chars (",
    show(chars[STATUS] div width), " lines)\n",
  "CODE:    ", show(chars[CODE]), " chars (",
    show(chars[CODE] div 80), " lines @ 80 cols)\n",
  "OUTPUT:  ", show(chars[OUTPUT]), " chars (",
    show(chars[OUTPUT] div width), " lines)\n",
  "DOCS:    ", show(chars[DOCS]), " chars (",
    show(chars[DOCS] div 80), " lines @ 80 cols)\n",
  "METRICS: ", show(chars[METRICS]), " chars (",
    show(chars[METRICS] div width), " lines)\n",
  "EMOJI:   ", show(chars[EMOJI]), " chars\n\n",
  "TOTAL:   ", show(sum(i in InfoType)(chars[i])), " / ", show(total_cells), " cells\n",
  "VALUE:   ", show(total_value), "\n\n",
  "LAYOUT:\n",
  "├─ Header (", show(chars[HEADER] div width), " lines)\n",
  "├─ Status (", show(chars[STATUS] div width), " lines)\n",
  "├─ Code   (", show(chars[CODE] div 80), " lines)\n",
  "├─ Output (", show(chars[OUTPUT] div width), " lines)\n",
  "├─ Docs   (", show(chars[DOCS] div 80), " lines)\n",
  "└─ Metrics (", show(chars[METRICS] div width), " lines)\n\n",
  "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
