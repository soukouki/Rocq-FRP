Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
From CoqFRP Require Import FRP OccsSteps AscTiming.
Import ListNotations.
Import Peano PeanoNat.Nat.

(*
以下はプリミティブに関する定理
OccsStepsに似ているが、これらの証明はAscTimingにも依存する
 *)

Lemma occs_merge_never_left a f (s : stream a) : occs (merge (never a) s f) = occs s.
Proof.
rewrite /=.
rewrite occs_knit_nil_left.
move : (is_asc_timing_occs s).
move : (occs s) => s0.
induction s0 as [ | [t1 a1] s1].
  by rewrite coalesce_equation.
move : IHs1.
case s1 => [ _ _ | [t2 a2] s2 IHs1 H1 ].
- by rewrite 2!coalesce_equation.
- rewrite coalesce_equation.
  have : t1 =? t2 = false => [ | -> ].
    rewrite eqb_neq.
    apply lt_neq.
    apply is_asc_timing_lt with (a0 := a1) (a' := a2) (s0 := (t2, a2) :: s2) => //.
    by apply in_eq.
  rewrite IHs1 => //.
  by apply is_asc_timing_tail in H1.
Qed.

Lemma occs_merge_never_right a f (s : stream a) : occs (merge s (never a) f) = occs s.
Proof.
rewrite /=.
rewrite occs_knit_nil_right.
move : (is_asc_timing_occs s).
move : (occs s) => s0.
induction s0 as [ | [t1 a1] s1] => [ _ | ].
  by rewrite coalesce_equation.
move : IHs1.
case s1 => [ _ _ | [t2 a2] s2 IHs1 H1].
- by rewrite 2!coalesce_equation.
- rewrite coalesce_equation.
  have : t1 =? t2 = false => [ | -> ].
    rewrite eqb_neq.
    apply lt_neq.
    apply is_asc_timing_lt with (a0 := a1) (a' := a2) (s0 := (t2, a2) :: s2) => //.
    by apply in_eq.
  rewrite IHs1 => //.
  by apply is_asc_timing_tail in H1.
Qed.






















