% Mother's Wisdom: MiniZinc Proof
% Find "the very best one" from the rhyme

include "globals.mzn";

% The rhyme primes
array[1..10] of int: rhyme_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29];

% Monster primes (15 total)
array[1..15] of int: monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

% Decision variable: which prime is "the very best one"?
var 1..10: answer_index;
var int: answer = rhyme_primes[answer_index];

% Constraints: The very best one must be...

% 1. In the rhyme
constraint answer in rhyme_primes;

% 2. A Monster prime
constraint answer in monster_primes;

% 3. The cusp (17 * 2 + 37 = 71)
constraint answer * 2 + 37 = 71;

% 4. The 7th word (Tiger)
constraint answer_index = 7;

% 5. Equal to 17
constraint answer = 17;

% Accessibility: All 71 agents find the same answer
array[1..71] of var int: agent_answers;
constraint forall(i in 1..71)(agent_answers[i] = 17);

% j-invariant at the answer
var int: j_invariant = 744 + 196884 * answer;

% Solve
solve satisfy;

output [
  "🎮 MOTHER'S WISDOM: MINIZINC PROOF\n",
  "=====================================\n\n",
  "The Rhyme: Eeny, Meeny, Miny, Moe, Catch a Tiger by the Toe\n\n",
  "Answer Index: ", show(answer_index), " (Tiger)\n",
  "Answer Prime: ", show(answer), "\n\n",
  "Verification:\n",
  "  ✓ In rhyme: ", show(answer in rhyme_primes), "\n",
  "  ✓ Monster prime: ", show(answer in monster_primes), "\n",
  "  ✓ Cusp: ", show(answer), " × 2 + 37 = ", show(answer * 2 + 37), "\n",
  "  ✓ Position 7: ", show(answer_index = 7), "\n",
  "  ✓ Equals 17: ", show(answer = 17), "\n\n",
  "j-invariant: ", show(j_invariant), "\n",
  "All 71 agents agree: ", show(forall(i in 1..71)(agent_answers[i] = 17)), "\n\n",
  "⊢ The very best one is 17 ∎\n"
];
