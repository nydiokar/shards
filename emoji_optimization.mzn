% MiniZinc: Calculate Best Emojis from All Inputs
% Optimize emoji selection for CICADA-71

% Parameters
int: num_shards = 71;
int: num_emojis = 20;  % Select best 20 emojis

% Emoji candidates (encoded as integers)
set of int: EMOJIS = 1..50;

% Emoji meanings (1-50)
% 1=🔮 2=⚡ 3=🕳️ 4=🛋️ 5=🌀 6=✨ 7=🎵 8=🔐 9=📐 10=🌊
% 11=🧮 12=🎭 13=🌙 14=⭐ 15=🔬 16=🎨 17=🏛️ 18=🌈 19=🔥 20=💫
% 21=🌸 22=🦋 23=🎪 24=🌺 25=🎯 26=🎲 27=🌻 28=🎰 29=🌷 30=🎸
% 31=🌹 32=🎹 33=🌼 34=🎺 35=🌾 36=🎻 37=🌿 38=🎼 39=🍀 40=🎤
% 41=🍁 42=🎧 43=🍂 44=🎬 45=🍃 46=🎭 47=🍄 48=🎨 49=🍅 50=🎪

% Decision variables: which emojis to select
array[1..num_emojis] of var EMOJIS: selected;

% Constraints

% All selected emojis must be different
constraint alldifferent(selected);

% Must include core emojis
constraint member(1, selected);  % 🔮 (Maass)
constraint member(2, selected);  % ⚡ (Energy)
constraint member(3, selected);  % 🕳️ (Hole)
constraint member(4, selected);  % 🛋️ (IKEA)
constraint member(8, selected);  % 🔐 (ZK)

% Emoji scores based on usage frequency
array[EMOJIS] of int: frequency = [
  42,  % 🔮 (used 42 times)
  71,  % ⚡ (used 71 times)
  12,  % 🕳️ (used 12 times)
  8,   % 🛋️ (used 8 times)
  15,  % 🌀 (used 15 times)
  37,  % ✨ (used 37 times)
  7,   % 🎵 (used 7 times)
  23,  % 🔐 (used 23 times)
  9,   % 📐 (used 9 times)
  11,  % 🌊 (used 11 times)
  5,   % 🧮 (used 5 times)
  6,   % 🎭 (used 6 times)
  13,  % 🌙 (used 13 times)
  19,  % ⭐ (used 19 times)
  4,   % 🔬 (used 4 times)
  8,   % 🎨 (used 8 times)
  3,   % 🏛️ (used 3 times)
  10,  % 🌈 (used 10 times)
  14,  % 🔥 (used 14 times)
  16,  % 💫 (used 16 times)
  2,   % 🌸 (used 2 times)
  3,   % 🦋 (used 3 times)
  4,   % 🎪 (used 4 times)
  2,   % 🌺 (used 2 times)
  5,   % 🎯 (used 5 times)
  6,   % 🎲 (used 6 times)
  3,   % 🌻 (used 3 times)
  4,   % 🎰 (used 4 times)
  2,   % 🌷 (used 2 times)
  5,   % 🎸 (used 5 times)
  3,   % 🌹 (used 3 times)
  4,   % 🎹 (used 4 times)
  2,   % 🌼 (used 2 times)
  3,   % 🎺 (used 3 times)
  2,   % 🌾 (used 2 times)
  3,   % 🎻 (used 3 times)
  2,   % 🌿 (used 2 times)
  3,   % 🎼 (used 3 times)
  2,   % 🍀 (used 2 times)
  3,   % 🎤 (used 3 times)
  2,   % 🍁 (used 2 times)
  3,   % 🎧 (used 3 times)
  2,   % 🍂 (used 2 times)
  3,   % 🎬 (used 3 times)
  2,   % 🍃 (used 2 times)
  3,   % 🎭 (used 3 times)
  2,   % 🍄 (used 2 times)
  3,   % 🎨 (used 3 times)
  2,   % 🍅 (used 2 times)
  3    % 🎪 (used 3 times)
];

% Emoji categories
array[EMOJIS] of int: category = [
  1,  % 🔮 Math/Magic
  1,  % ⚡ Energy
  2,  % 🕳️ Hole
  3,  % 🛋️ IKEA
  1,  % 🌀 Math
  1,  % ✨ Magic
  4,  % 🎵 Music
  5,  % 🔐 Security
  1,  % 📐 Math
  1,  % 🌊 Nature
  1,  % 🧮 Math
  4,  % 🎭 Art
  1,  % 🌙 Celestial
  1,  % ⭐ Celestial
  1,  % 🔬 Science
  4,  % 🎨 Art
  1,  % 🏛️ Architecture
  1,  % 🌈 Nature
  1,  % 🔥 Energy
  1,  % 💫 Celestial
  6,  % 🌸 Flowers
  6,  % 🦋 Nature
  4,  % 🎪 Entertainment
  6,  % 🌺 Flowers
  4,  % 🎯 Games
  4,  % 🎲 Games
  6,  % 🌻 Flowers
  4,  % 🎰 Games
  6,  % 🌷 Flowers
  4,  % 🎸 Music
  6,  % 🌹 Flowers
  4,  % 🎹 Music
  6,  % 🌼 Flowers
  4,  % 🎺 Music
  6,  % 🌾 Nature
  4,  % 🎻 Music
  6,  % 🌿 Nature
  4,  % 🎼 Music
  6,  % 🍀 Nature
  4,  % 🎤 Music
  6,  % 🍁 Nature
  4,  % 🎧 Music
  6,  % 🍂 Nature
  4,  % 🎬 Entertainment
  6,  % 🍃 Nature
  4,  % 🎭 Art
  6,  % 🍄 Nature
  4,  % 🎨 Art
  6,  % 🍅 Food
  4   % 🎪 Entertainment
];

% Diversity constraint: at least 3 different categories
constraint sum(i in 1..num_emojis)(
  exists(j in 1..num_emojis where j != i)(
    category[selected[i]] != category[selected[j]]
  )
) >= 15;

% Objective: Maximize total frequency score
var int: total_score = sum(i in 1..num_emojis)(frequency[selected[i]]);

solve maximize total_score;

% Output
output [
  "Best " ++ show(num_emojis) ++ " Emojis for CICADA-71:\n",
  "Total Score: " ++ show(total_score) ++ "\n\n",
  "Selected Emojis (by ID):\n"
] ++
[
  show(selected[i]) ++ " " 
  | i in 1..num_emojis
] ++
["\n\nEmoji Mapping:\n"] ++
[
  if selected[i] == 1 then "🔮 "
  else if selected[i] == 2 then "⚡ "
  else if selected[i] == 3 then "🕳️ "
  else if selected[i] == 4 then "🛋️ "
  else if selected[i] == 5 then "🌀 "
  else if selected[i] == 6 then "✨ "
  else if selected[i] == 7 then "🎵 "
  else if selected[i] == 8 then "🔐 "
  else if selected[i] == 13 then "🌙 "
  else if selected[i] == 14 then "⭐ "
  else if selected[i] == 19 then "🔥 "
  else if selected[i] == 20 then "💫 "
  else "? "
  endif endif endif endif endif endif endif endif endif endif endif endif
  | i in 1..num_emojis
] ++
["\n"];
