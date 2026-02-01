% MiniZinc: English ↔ Emoji Translator
% Constraint-based translation

% Word to emoji mapping (71 words for 71 shards)
enum WORD = {
  MAGIC, ENERGY, HOLE, IKEA, SPIRAL, SPARKLE, MUSIC, LOCK, MATH, WAVE,
  ABACUS, MASK, MOON, STAR, SCIENCE, ART, TEMPLE, RAINBOW, FIRE, COMET,
  FLOWER, BUTTERFLY, CIRCUS, TARGET, DICE, GUITAR, PIANO, TRUMPET, VIOLIN,
  NATURE, LEAF, CLOVER, MAPLE, HEADPHONES, FILM, MUSHROOM, TOMATO,
  HECKE, MAASS, MOCK, SHADOW, HARMONIC, ZEN, PROOF, SHARD, JAIL, SUS,
  PRIME, GANDALF, ETERNAL, EPHEMERAL, ONTOLOGY, OPERATOR, FORM, MODULAR,
  AUTOMORPHIC, MOONSHINE, MONSTER, GROUP, SUPERSINGULAR, ELLIPTIC, CURVE,
  INVARIANT, COEFFICIENT, THEOREM, LEMMA, CONJECTURE, AXIOM, QED, VERIFY,
  WITNESS, GROTH16
};

% Emoji codes (1-71)
array[WORD] of int: emoji_code = [
  1,2,3,4,5,6,7,8,9,10,  % MAGIC-WAVE
  11,12,13,14,15,16,17,18,19,20,  % ABACUS-COMET
  21,22,23,24,25,26,27,28,29,30,  % FLOWER-NATURE
  31,32,33,34,35,36,37,38,39,40,  % LEAF-MOCK
  41,42,43,44,45,46,47,48,49,50,  % SHADOW-EPHEMERAL
  51,52,53,54,55,56,57,58,59,60,  % ONTOLOGY-ELLIPTIC
  61,62,63,64,65,66,67,68,69,70,71  % CURVE-GROTH16
];

% Decision: translate sentence
int: max_words = 10;
array[1..max_words] of var WORD: sentence;
array[1..max_words] of var 1..71: emojis;

% Constraint: each word maps to its emoji
constraint forall(i in 1..max_words)(
  emojis[i] = emoji_code[sentence[i]]
);

% Example: "MAGIC ENERGY HOLE" → 🔮⚡🕳️
constraint sentence[1] = MAGIC;
constraint sentence[2] = ENERGY;
constraint sentence[3] = HOLE;

solve satisfy;

output ["Words: "] ++ [show(sentence[i]) ++ " " | i in 1..3] ++
       ["\nEmojis: "] ++ [show(emojis[i]) ++ " " | i in 1..3];
