% MiniZinc model for efficiency optimization

% Parameters
int: num_agents = 71;
int: num_capabilities = 6;

% Decision variables
array[1..num_agents] of var 0..70: shard_ids;
array[1..num_agents] of var 1..1000: generation_time_ms;

% Constraints
% 1. All shard_ids must be unique
constraint alldifferent(shard_ids);

% 2. Shard IDs must be in range [0, 70]
constraint forall(i in 1..num_agents) (
    shard_ids[i] >= 0 /\ shard_ids[i] <= 70
);

% 3. Generation time must be reasonable (< 100ms per agent)
constraint forall(i in 1..num_agents) (
    generation_time_ms[i] <= 100
);

% 4. Total generation time should be minimized
var int: total_time = sum(generation_time_ms);

% Objective: Minimize total generation time
solve minimize total_time;

% Output
output [
    "Optimal agent generation:\n",
    "Total time: ", show(total_time), " ms\n",
    "Average time per agent: ", show(total_time div num_agents), " ms\n",
    "Shard IDs: ", show(shard_ids), "\n"
];
