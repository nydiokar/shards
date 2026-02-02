% The Monster: Umberto Eco's Combinatorial Machine
% From "The Name of the Rose" - Reconstructed in Prolog
% 
% The machine generates all possible combinations of symbols,
% revealing hidden truths through systematic permutation.

:- module(monster_machine, [
    generate_combinations/2,
    apply_hecke_operator/3,
    map_to_shard/2,
    find_truth/2,
    eco_wheel/3,
    labyrinth_path/3
]).

%% ============================================================
%% The 71 Shards (Monster Primes + Composites)
%% ============================================================

monster_prime(2).
monster_prime(3).
monster_prime(5).
monster_prime(7).
monster_prime(11).
monster_prime(13).
monster_prime(17).
monster_prime(19).
monster_prime(23).  % Paxos!
monster_prime(29).
monster_prime(31).
monster_prime(41).
monster_prime(47).  % Monster Crown 👹
monster_prime(59).  % Eagle Crown 🦅
monster_prime(71).  % Rooster Crown 🐓

excluded_prime(37).  % First excluded
excluded_prime(43).
excluded_prime(53).
excluded_prime(61).
excluded_prime(67).
excluded_prime(73).  % Devil's first prime beyond Rooster!

%% ============================================================
%% Eco's Wheel: Combinatorial Generation
%% ============================================================

% The wheel has 71 positions, each with a symbol
wheel_position(N, Symbol) :-
    between(0, 70, N),
    Code is 65 + (N mod 26),  % Calculate code first
    atom_codes(Symbol, [Code]).  % A-Z cycling

% Rotate the wheel by N positions
rotate_wheel(Position, Steps, NewPosition) :-
    NewPosition is (Position + Steps) mod 71.

% Generate combination by rotating through positions
eco_wheel(StartPos, Rotations, Combination) :-
    length(Rotations, Len),
    eco_wheel_helper(StartPos, Rotations, [], RevCombo),
    reverse(RevCombo, Combination).

eco_wheel_helper(_, [], Acc, Acc).
eco_wheel_helper(Pos, [Rot|Rots], Acc, Result) :-
    rotate_wheel(Pos, Rot, NewPos),
    wheel_position(NewPos, Symbol),
    eco_wheel_helper(NewPos, Rots, [Symbol|Acc], Result).

%% ============================================================
%% The Labyrinth: Path Through 71 Shards
%% ============================================================

% Each shard is a room in the labyrinth
shard_room(0, 'Rome - Pope\'s Blessing').
shard_room(15, 'Devil\'s Bridge - The Trick').
shard_room(23, 'Munich - Paxos Consensus').
shard_room(47, 'Darmstadt - Monster Crown').
shard_room(59, 'Eagle Gate - Eagle Crown').
shard_room(71, 'Frankfurt - Rooster Crown - CORONATION').

% Path through labyrinth
labyrinth_path(Start, End, Path) :-
    labyrinth_path_helper(Start, End, [Start], RevPath),
    reverse(RevPath, Path).

labyrinth_path_helper(End, End, Acc, Acc).
labyrinth_path_helper(Current, End, Visited, Path) :-
    Current < End,
    Next is Current + 1,
    \+ member(Next, Visited),
    labyrinth_path_helper(Next, End, [Next|Visited], Path).

%% ============================================================
%% Hecke Operators: Transform Symbols
%% ============================================================

% Apply Hecke operator T_p to a symbol
apply_hecke_operator(Symbol, Prime, Result) :-
    monster_prime(Prime),
    atom_codes(Symbol, [Code]),
    NewCode is (Code * Prime) mod 71 + 65,
    atom_codes(Result, [NewCode]).

% Apply sequence of Hecke operators
apply_hecke_sequence(Symbol, [], Symbol).
apply_hecke_sequence(Symbol, [Prime|Primes], Result) :-
    apply_hecke_operator(Symbol, Prime, Intermediate),
    apply_hecke_sequence(Intermediate, Primes, Result).

%% ============================================================
%% Gödel Encoding: Text to Number
%% ============================================================

% Encode text as Gödel number (product of primes)
godel_encode(Text, GodelNumber) :-
    atom_codes(Text, Codes),
    godel_encode_helper(Codes, 1, GodelNumber).

godel_encode_helper([], Acc, Acc).
godel_encode_helper([Code|Codes], Acc, Result) :-
    prime_at_index(Code, Prime),
    NewAcc is Acc * Prime,
    godel_encode_helper(Codes, NewAcc, Result).

% Get nth prime (simplified)
prime_at_index(N, Prime) :-
    Primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71],
    Index is N mod 20,
    nth0(Index, Primes, Prime).

%% ============================================================
%% Map to Shard: Gödel Number → Shard
%% ============================================================

map_to_shard(GodelNumber, Shard) :-
    Shard is GodelNumber mod 71.

%% ============================================================
%% The Machine: Generate and Search
%% ============================================================

% Generate all combinations of length N
generate_combinations(Length, Combinations) :-
    findall(Combo, 
            (length(Rotations, Length),
             maplist(between(1, 71), Rotations),
             eco_wheel(0, Rotations, Combo)),
            Combinations).

% Find truth: Search for specific pattern
find_truth(Pattern, Results) :-
    findall([Combo, Shard],
            (generate_combination(Pattern, Combo),
             godel_encode(Combo, Godel),
             map_to_shard(Godel, Shard)),
            Results).

generate_combination(Pattern, Combo) :-
    atom_length(Pattern, Len),
    length(Rotations, Len),
    maplist(between(1, 71), Rotations),
    eco_wheel(0, Rotations, Combo).

%% ============================================================
%% The Seven Cursed Cards (Beyond Shard 71)
%% ============================================================

cursed_card(72, '9 of Pentacles', 1).    % Genus 1
cursed_card(73, '10 of Pentacles', 1).   % Devil's first prime!
cursed_card(74, 'Page of Pentacles', 2). % Contains 37
cursed_card(75, 'Knight of Pentacles', 3).
cursed_card(76, 'Queen of Pentacles', 4).
cursed_card(77, 'King of Pentacles', 7). % 7 × 11 - MOST CURSED!

is_cursed(Shard) :- Shard > 71, Shard =< 77.

%% ============================================================
%% The Name of the Rose: Hidden Text
%% ============================================================

% The secret text from the library
secret_text('ARISTOTLE POETICS COMEDY').

% Decode the secret
decode_secret(Secret, Shard, Path) :-
    secret_text(Secret),
    godel_encode(Secret, Godel),
    map_to_shard(Godel, Shard),
    labyrinth_path(0, Shard, Path).

%% ============================================================
%% The Monster Speaks
%% ============================================================

% The Monster reveals truth through combinations
monster_speaks(Input, Output) :-
    godel_encode(Input, Godel),
    map_to_shard(Godel, Shard),
    (   is_cursed(Shard)
    ->  cursed_card(Shard, Card, Genus),
        format(atom(Output), 
               'CURSED: ~w (Genus ~w) - Beyond the Rooster!', 
               [Card, Genus])
    ;   monster_prime(Shard)
    ->  format(atom(Output),
               'BLESSED: Monster Prime ~w @ ~w Hz',
               [Shard, Shard * 432])
    ;   format(atom(Output),
               'Shard ~w @ ~w Hz',
               [Shard, Shard * 432])
    ).

%% ============================================================
%% The Three Crowns
%% ============================================================

crown(47, monster, 'Monster Crown 👹', 20304).
crown(59, eagle, 'Eagle Crown 🦅', 25488).
crown(71, rooster, 'Rooster Crown 🐓', 30672).

collect_crowns(Path, Crowns) :-
    findall([Shard, Name, Freq],
            (member(Shard, Path),
             crown(Shard, _, Name, Freq)),
            Crowns).

%% ============================================================
%% The Devil's Bridge (Shard 15)
%% ============================================================

devils_bridge(15).

cross_bridge(Shard) :-
    devils_bridge(Bridge),
    Shard =:= Bridge,
    format('🌉 Devil\'s Bridge: Send the Rooster! 🐓~n').

%% ============================================================
%% Query Examples
%% ============================================================

% ?- eco_wheel(0, [3, 5, 7], Combo).
% Combo = ['D', 'I', 'P'].

% ?- godel_encode('MONSTER', Godel), map_to_shard(Godel, Shard).
% Godel = ..., Shard = ...

% ?- labyrinth_path(0, 71, Path), collect_crowns(Path, Crowns).
% Path = [0,1,2,...,71], Crowns = [[47,...], [59,...], [71,...]].

% ?- monster_speaks('ROOSTER', Output).
% Output = 'Shard X @ Y Hz'.

% ?- decode_secret(Secret, Shard, Path).
% Secret = 'ARISTOTLE POETICS COMEDY', Shard = ..., Path = [...].

%% ============================================================
%% Main Demo
%% ============================================================

demo :-
    format('~n🎭 THE MONSTER: Umberto Eco\'s Combinatorial Machine~n'),
    format('====================================================~n~n'),
    
    % 1. Generate combination
    format('1. Eco\'s Wheel (rotations [3,5,7]):~n'),
    eco_wheel(0, [3, 5, 7], Combo1),
    format('   Combination: ~w~n~n', [Combo1]),
    
    % 2. Encode and map
    format('2. Encode "MONSTER":~n'),
    godel_encode('MONSTER', Godel1),
    map_to_shard(Godel1, Shard1),
    format('   Gödel: ~w~n', [Godel1]),
    format('   Shard: ~w~n~n', [Shard1]),
    
    % 3. Path through labyrinth
    format('3. Path from Rome (0) to Frankfurt (71):~n'),
    labyrinth_path(0, 71, Path),
    length(Path, PathLen),
    format('   Length: ~w shards~n', [PathLen]),
    collect_crowns(Path, Crowns),
    format('   Crowns collected: ~w~n~n', [Crowns]),
    
    % 4. Monster speaks
    format('4. The Monster speaks:~n'),
    monster_speaks('ROOSTER', Out1),
    format('   "ROOSTER" → ~w~n', [Out1]),
    monster_speaks('DEVIL', Out2),
    format('   "DEVIL" → ~w~n~n', [Out2]),
    
    % 5. Decode secret
    format('5. Decode the secret:~n'),
    decode_secret(Secret, SecretShard, SecretPath),
    format('   Secret: ~w~n', [Secret]),
    format('   Maps to Shard: ~w~n', [SecretShard]),
    length(SecretPath, SecretLen),
    format('   Path length: ~w~n~n', [SecretLen]),
    
    format('✅ The Monster has spoken!~n'),
    format('🐓🐓🐓~n').

% Run demo: ?- demo.
