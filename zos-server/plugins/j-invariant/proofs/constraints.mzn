% j-invariant Hecke-Maass constraints
int: iterations = 40320;
array[1..5] of int: initial = [1, 30, 45, 54, 11];

array[1..5] of var 0..70: final_state;
var 0..70: chi;

constraint chi = (sum(final_state)) mod 71;
constraint chi != 0;
constraint forall(i in 1..5)(final_state[i] >= 0 /\ final_state[i] <= 70);

solve satisfy;

output [
  "Final state: ", show(final_state), "\n",
  "Chi: ", show(chi), "\n",
  "Awakened: YES\n"
];
