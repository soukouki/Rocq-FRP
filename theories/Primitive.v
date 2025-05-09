Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
From CoqFRP Require Import FRP OccsSteps AscTiming.
Import ListNotations.
Import Peano PeanoNat.Nat.

Definition lift a b c (ca : cell a) (cb : cell b) (f : a -> b -> c) : cell c := apply (map_c f ca) cb.

Definition gate a (s : stream a) (c : cell bool) : stream a :=
  map_s fst (filter (fun ac => snd ac) (snapshot (fun a' cond => (a', cond)) s c)).

(* 以下はプリミティブに関する定理 *)

Theorem occs_map_never a b (f : a -> b) : occs (map_s f (never a)) = occs (never b).
Proof. by []. Qed.

Theorem occs_merge_never_right a f (s : stream a) : occs (merge s (never a) f) = occs s.
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
    apply in_eq.
  rewrite IHs1 => //.
  by apply is_asc_timing_tail in H1.
Qed.

Theorem occs_merge_never_left a f (s : stream a) : occs (merge (never a) s f) = occs s.
Proof.
rewrite /=.
rewrite occs_knit_equation /=.
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
    apply in_eq.
  rewrite IHs1 => //.
  by apply is_asc_timing_tail in H1.
Qed.
