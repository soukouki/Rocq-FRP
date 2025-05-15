
From Ltac2 Require Import Ltac2.

Definition a := 42.

Ltac2 clause_concl := {Std.on_hyps := None; Std.on_concl := Std.AllOccurrences}.

Section A.

Variable b : nat.

Ltac2 f (a: constr) := Message.print (Message.of_string "test").

Theorem T : a = 42.
Proof.
f '(1+1).

Std.unfold [(reference:(a)), Std.AllOccurrences] clause_concl. (* OK *)
Undo.
Std.unfold [(Std.VarRef(ident:(a))), Std.AllOccurrences] clause_concl.
(* => Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/. *)

(* 
versions:
coq-core   9.0.0       Compatibility binaries for Coq after the Rocq renaming
coq-stdlib 9.0.0       Compatibility metapackage for Coq Stdlib library after the Rocq renaming
 *)
