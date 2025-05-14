Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP .
From Ltac2 Require Import Ltac2 Init Std Message.

Definition Test := list nat.
Hint Unfold Test : frp.

Ltac2 foo_ () := 
Ltac2 Notation foo := foo_ ().

Goal forall A B : Prop, A -> B -> (A->B).
intros A B H.
foo.
Restart.
match! goal with
| [ h1 : _, h2 : _ |- _ ] =>
   print (concat (of_string "match ")
         (concat (of_constr (Control.hyp h1))
         (concat (of_string " ")
         (of_constr (Control.hyp h2)))));
   fail
| [ |- _ ] => ()
end.

Admitted.