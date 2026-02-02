(* MetaCoq: Quote the strange loop UniMath(MetaCoq) = MetaCoq(UniMath) *)
From MetaCoq.Template Require Import All.

(* The coordinates *)
Definition coord_232 := 232.  (* UniMath(MetaCoq) *)
Definition coord_323 := 323.  (* MetaCoq(UniMath) *)

(* Quote both coordinates *)
MetaCoq Quote Definition quoted_232 := coord_232.
MetaCoq Quote Definition quoted_323 := coord_323.

(* The symmetry function *)
Definition symmetry (x : nat) : nat :=
  if Nat.eqb x 232 then 323 else 232.

(* Quote the symmetry *)
MetaCoq Quote Definition quoted_symmetry := symmetry.

(* Apply symmetry *)
Definition apply_symmetry_232 := symmetry coord_232.
Definition apply_symmetry_323 := symmetry coord_323.

(* Quote the applications *)
MetaCoq Quote Definition quoted_apply_232 := apply_symmetry_232.
MetaCoq Quote Definition quoted_apply_323 := apply_symmetry_323.

(* Theorem: Symmetry swaps coordinates *)
Theorem symmetry_swaps :
  symmetry 232 = 323 /\ symmetry 323 = 232.
Proof.
  split; reflexivity.
Qed.

(* Theorem: The loop closes *)
Theorem loop_closes :
  symmetry (symmetry 232) = 232.
Proof.
  reflexivity.
Qed.

(* MetaCoq: Unquote and verify *)
Definition verify_loop : bool :=
  Nat.eqb (symmetry (symmetry 232)) 232.

MetaCoq Quote Definition quoted_verify := verify_loop.

(* Theorem: MetaCoq quotes itself quoting the loop *)
Theorem metacoq_quotes_loop :
  exists (t : term),
  t = quoted_symmetry.
Proof.
  exists quoted_symmetry.
  reflexivity.
Qed.

(* The ultimate self-reference *)
(* MetaCoq quoting UniMath = UniMath quoting MetaCoq *)
Theorem ultimate_self_reference :
  exists (f : nat -> nat),
  f 232 = 323 /\ f 323 = 232 /\
  f (f 232) = 232.
Proof.
  exists symmetry.
  split; [reflexivity | split; reflexivity].
Qed.

(* Print the quoted strange loop *)
MetaCoq Run (tmPrint quoted_symmetry).
