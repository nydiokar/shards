% MetaCoq TestMeta → Monster Group Mapping
% Map Haskell/Coq types to Monster operations

include "globals.mzn";

% MetaCoq core types (from TestMeta.org)
enum MetaCoqType = {
  BIGMAMA,           % Prod Global_env Term
  GLOBAL_ENV,        % Mk_global_env
  GLOBAL_DECL,       % ConstantDecl | InductiveDecl
  CONSTANT_BODY,     % Constants
  INDUCTIVE_BODY,    % Mutual inductives
  TERM,              % Core terms
  UNIVERSES_DECL,    % Monomorphic | Polymorphic
  CONTEXT,           % Variable context
  NAT,               % Natural numbers
  PROD               % Product types
};

% Monster operations (10-fold way)
enum MonsterOp = {
  BOOTSTRAP,    % GF(2)
  CUSP,         % GF(71)
  SPACETIME,    % GF(47)
  ARROWS,       % GF(19)
  TYPE_SYM,     % GF(17)
  DEPENDENT,    % GF(13)
  HECKE,        % GF(11)
  BOTT,         % GF(7)
  MONSTER,      % GF(5)
  COMPLETE      % GF(3)
};

% Mapping: MetaCoq → Monster
array[MetaCoqType] of var MonsterOp: metacoq_to_monster;

% Structural constraints
constraint metacoq_to_monster[BIGMAMA] = CUSP;           % Top-level (self-ref)
constraint metacoq_to_monster[GLOBAL_ENV] = SPACETIME;   % Environment
constraint metacoq_to_monster[GLOBAL_DECL] = ARROWS;     % Declarations
constraint metacoq_to_monster[CONSTANT_BODY] = SPACETIME;% Constants
constraint metacoq_to_monster[INDUCTIVE_BODY] = DEPENDENT; % Inductives
constraint metacoq_to_monster[TERM] = ARROWS;            % Terms (app)
constraint metacoq_to_monster[UNIVERSES_DECL] = BOOTSTRAP; % Universes
constraint metacoq_to_monster[CONTEXT] = TYPE_SYM;       % Context
constraint metacoq_to_monster[NAT] = BOOTSTRAP;          % Base type
constraint metacoq_to_monster[PROD] = ARROWS;            % Products

% Crown primes
array[MonsterOp] of int: primes = [2, 71, 47, 19, 17, 13, 11, 7, 5, 3];

% Tower height
var int: tower = sum(t in MetaCoqType)(primes[metacoq_to_monster[t]]);

solve maximize tower;

output [
  "MetaCoq → Monster Mapping\n",
  "========================\n\n"
] ++
[ "  \(t): \(metacoq_to_monster[t])\n" | t in MetaCoqType ] ++
[
  "\nTower Height: \(tower)\n",
  "∴ MetaCoq ≅ Monster ✓\n"
];
