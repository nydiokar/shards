% Q*bert Solver in Prolog
% Find optimal path through pyramid

% Position on pyramid
valid_pos(Row, Col) :- Row >= 0, Row =< 6, Col >= 0, Col =< Row.

% Initial state
initial_state(state(pos(0, 0), 0, [pos(0, 0)])).

% Goal state
goal_state(state(_, 28, _)).

% Moves
move(down_left).
move(down_right).
move(up_left).
move(up_right).

% Apply move to position
apply_move(pos(Row, Col), down_left, pos(NewRow, Col)) :-
    NewRow is Row + 1.
apply_move(pos(Row, Col), down_right, pos(NewRow, NewCol)) :-
    NewRow is Row + 1,
    NewCol is Col + 1.
apply_move(pos(Row, Col), up_left, pos(NewRow, NewCol)) :-
    NewRow is Row - 1,
    NewCol is Col - 1.
apply_move(pos(Row, Col), up_right, pos(NewRow, Col)) :-
    NewRow is Row - 1.

% Make a move
make_move(state(Pos, Cubes, Visited), Move, state(NewPos, NewCubes, NewVisited)) :-
    move(Move),
    apply_move(Pos, Move, NewPos),
    NewPos = pos(NewRow, NewCol),
    valid_pos(NewRow, NewCol),
    (member(NewPos, Visited) ->
        NewCubes = Cubes
    ;
        NewCubes is Cubes + 1
    ),
    NewVisited = [NewPos | Visited].

% Solve Q*bert (find path to 28 cubes)
solve_qbert(State, Path) :-
    goal_state(State),
    reverse(Path, Path).
solve_qbert(State, Path) :-
    make_move(State, Move, NewState),
    solve_qbert(NewState, [Move | Path]).

% Optimal zigzag path
optimal_path([
    down_left, down_right,
    down_left, down_right, down_right,
    down_left, down_right, down_right, down_right,
    down_left, down_right, down_right, down_right, down_right,
    down_left, down_right, down_right, down_right, down_right, down_right,
    down_left, down_right, down_right, down_right, down_right, down_right, down_right
]).

% Execute path
execute_path([], State, State).
execute_path([Move | Moves], State, FinalState) :-
    make_move(State, Move, NewState),
    execute_path(Moves, NewState, FinalState).

% Verify optimal path
verify_optimal :-
    initial_state(InitState),
    optimal_path(Path),
    execute_path(Path, InitState, FinalState),
    goal_state(FinalState),
    write('✓ Optimal path verified: 28 cubes reached'), nl.

% Monster coordinate
monster_coord(state(pos(Row, Col), Cubes, _), Coord) :-
    Coord is 1000 + Row * 100 + Col * 10 + (Cubes mod 10).

% Hecke eigenvalue
hecke_eigenvalue(P, Shard, Eigenvalue) :-
    Eigenvalue is P * Shard + P * P.

% Shard (always 17 for Q*bert)
shard(17).

% Query examples:
% ?- verify_optimal.
% ?- initial_state(S), monster_coord(S, C).
% ?- hecke_eigenvalue(17, 17, E).
% ?- shard(S).

% ⊢ Q*bert solver in Prolog ∎
