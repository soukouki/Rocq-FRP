Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.
From Ltac2 Require Import Ltac2 Message.

Goal forall A B : Prop, A -> B -> (A->B).
intros A B H.
match! goal with
| [ h1 : _, h2 : _ |- _ ] =>
   print (concat (of_string "match ")
         (concat (of_constr (Control.hyp h1))
         (concat (of_string " ")
         (of_constr (Control.hyp h2)))));
   fail
| [ |- _ ] => ()
end.

Ltac2 foo () := apply stream_timing_snapshot.
