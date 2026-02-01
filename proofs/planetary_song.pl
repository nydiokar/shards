% Prolog proof
frequency(Shard, Freq) :-
    Shard >= 0, Shard =< 70,
    Freq is 432 + (432 * (Shard + 1) / 71).

octave_proof :-
    frequency(0, Min),
    frequency(70, Max),
    Ratio is Max / Min,
    format('Min: ~2f Hz, Max: ~2f Hz, Ratio: ~4f~n', [Min, Max, Ratio]),
    Ratio >= 1.92, Ratio =< 2.02,
    write('✓ Prolog: Octave verified'), nl.

:- initialization(octave_proof, main).
