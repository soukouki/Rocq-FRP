Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
From CoqFRP Require Import FRP OccsSteps.
Import ListNotations.
Import Peano PeanoNat.Nat.

(* 以下はis_asc_timingに関する補題 *)

Lemma is_asc_timing_tail a (tp1 : time * a) tps1 :
  is_asc_timing (tp1 :: tps1) = true -> is_asc_timing tps1 = true.
Proof.
case tp1 => t1 a1.
case tps1 => // tp2 tps2; clear tps1.
case tp2 => t2 a2.
rewrite /= => H1.
rewrite Bool.andb_true_iff in H1.
by case H1.
Qed.

Lemma is_asc_timing_head a t0 a0 (s0 : str a) :
  is_asc_timing s0 = true ->
  (forall t' a', In (t', a') s0 -> t0 < t') ->
  is_asc_timing ((t0, a0) :: s0) = true.
Proof.
move => H1 H2.
rewrite /=.
rewrite H1.
move : H2.
case s0 => // [[t1 a1] s1] H3.
rewrite Bool.andb_true_r.
rewrite ltb_lt.
apply H3 with (a' := a1).
by apply in_eq.
Qed.

Lemma is_asc_timing_head_lt a t0 a0 t1 a1 (s1 : str a) :
  is_asc_timing ((t0, a0) :: (t1, a1) :: s1) = true ->
  t0 < t1.
Proof.
rewrite /is_asc_timing.
rewrite Bool.andb_true_iff.
case => H1 _.
by apply ltb_lt in H1.
Qed.

Lemma is_asc_timing_lt a t0 a0 (s0 : str a) :
  is_asc_timing ((t0, a0) :: s0) = true ->
  forall t' a', In (t', a') s0 -> t0 < t'.
Proof.
move : t0 a0.
induction s0 as [ | [t1 a1] s1 ] => //.
move => t0 a0 H1 t' a' /= H2.
case H2 => H3.
- inversion H3.
  subst; clear H2 H3.
  by apply is_asc_timing_head_lt in H1.
- apply IHs1 with (a0 := a0) (a' := a') => //.
  move : H1.
  case s1 => [ | [t2 a2] s2 ] => //= H4.
  rewrite Bool.andb_true_iff in H4.
  case H4 => H5 H6.
  rewrite Bool.andb_true_iff in H6.
  case H6 => H7 H8.
  clear IHs1 H2 H4 H6.
  rewrite Bool.andb_true_iff.
  split => //.
  rewrite ltb_lt.
  rewrite 2!ltb_lt in H5 H7.
  by apply (lt_trans _ _ _ H5 H7).
Qed.

Lemma is_asc_timing_first_lt a (ta1 ta2 : time * a) tas2 :
  is_asc_timing (ta1 :: ta2 :: tas2) = true -> fst ta1 <? fst ta2 = true.
Proof.
case ta1 => t1 a1.
case ta2 => t2 a2.
rewrite /= => H1.
rewrite Bool.andb_true_iff in H1.
by case H1.
Qed.

Lemma is_asc_timing_map_s p a (f : p -> a) (s : stream p) :
  is_asc_timing (occs s) = true -> is_asc_timing (occs (map_s f s)) = true.
Proof.
rewrite /=.
move : (occs s) => tas0 H1.
induction tas0 as [ | ta1 tas1 IH ] => //=.
rewrite IH; clear IH.
- by apply is_asc_timing_tail in H1.
- move : tas1 H1.
  case => // ta2 tas2 H1.
  rewrite /=.
  rewrite Bool.andb_true_iff.
  split => //.
  by apply is_asc_timing_first_lt in H1.
Qed.

Lemma is_asc_timing_snapshot a prev_s prev_c (f : prev_s -> prev_c -> a) (s : stream prev_s) (c : cell prev_c) :
  is_asc_timing (occs s) = true -> is_asc_timing (occs (snapshot f s c)) = true.
Proof.
rewrite /=.
move : (occs s) => tas0 H1.
induction tas0 as [ | ta1 tas1 IH ] => //=.
rewrite IH; clear IH.
- by apply is_asc_timing_tail in H1.
- move: tas1 H1.
  case => // ta2 tas2 H1.
  rewrite /=.
  rewrite Bool.andb_true_iff.
  split => //.
  by apply is_asc_timing_first_lt in H1.
Qed.

Lemma is_asc_timing_to_coalesce_eq a (s : str a) (f : a -> a -> a) :
  is_asc_timing s = true -> coalesce f s = s.
Proof.
induction s as [ | [t1 a1] s1 ].
  by rewrite coalesce_equation.
move : IHs1.
case s1 => [ | [t2 a2] s2 ] => IHs1 H1.
  by rewrite 2!coalesce_equation.
rewrite coalesce_equation.
have : (t1 =? t2) = false => [ | -> ].
  rewrite eqb_neq.
  apply lt_neq.
  apply (is_asc_timing_lt _ _ _ H1 _ a2).
  by left.
rewrite IHs1 => //.
by apply is_asc_timing_tail in H1.
Qed.

Lemma is_asc_timing_coalesce a (s : str a) (f : a -> a -> a) :
  is_asc_timing s = true -> is_asc_timing (coalesce f s) = true.
Proof.
move => H1.
by rewrite is_asc_timing_to_coalesce_eq.
Qed.

Lemma coalesce_min_le a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  ta0 <= tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, sb0)).
Proof.
Admitted.

Lemma coalesce_min_lt_right a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  ta0 < tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, (tb0, b0) :: sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, (tb0, b0) :: sb0)).
Proof.
Admitted.

Lemma coalesce_min_lt_left a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  tb0 < ta0 ->
  coalesce f ((tb0, b0) :: occs_knit ((ta0, a0) :: sa0, sb0)) = (ta0, a0) :: coalesce f(occs_knit ((ta0, a0) :: sa0, sb0)).
Proof.
Admitted.

Lemma occs_knit_min a ta0 a0 sa0 tb0 (b0 : a) sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  ta0 <= tb0 ->
  occs_knit (sa0, (tb0, b0) :: sb0) = (tb0, b0) :: occs_knit (sa0, sb0).
Proof.
Admitted.

Lemma is_asc_timing_min_coalesce_occs_knit a (f : a -> a -> a) (t1 ta2 : time) (a1 a2 b1 : a) (sa2 sb1 : str a) :
  is_asc_timing ((t1, a1) :: (ta2, a2) :: sa2) = true ->
  is_asc_timing ((t1, b1) :: sb1) = true ->
  is_asc_timing ((t1, f a1 b1) :: coalesce f (occs_knit ((ta2, a2) :: sa2, sb1))) = true.
Proof.
Admitted.

Lemma coalesce_occs_knit_exists_right a (f : a -> a -> a) (ta1 tb1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  is_asc_timing ((ta1, a1) :: sa1) = true ->
  is_asc_timing ((tb1, b1) :: sb1) = true ->
  exists tm1 m1 sm1,
    coalesce f (occs_knit (sa1, (tb1, b1) :: sb1)) = (tm1, m1) :: sm1 /\ ta1 < tm1.
Admitted.

Lemma coalesce_occs_knit_exists_left a (f : a -> a -> a) (ta1 tb1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  is_asc_timing ((ta1, a1) :: sa1) = true ->
  is_asc_timing ((tb1, b1) :: sb1) = true ->
  exists tm1 m1 sm1,
    coalesce f (occs_knit ((ta1, a1) :: sa1, sb1)) = (tm1, m1) :: sm1 /\ ta1 < tm1.
Admitted.

Lemma is_asc_timing_merge a (sa sb : stream a) (f : a -> a -> a) :
  is_asc_timing (occs sa) = true ->
  is_asc_timing (occs sb) = true ->
  is_asc_timing (occs (merge sa sb f)) = true.
Proof.
rewrite /=.
move : (occs sa) (occs sb) => sa0 sb0; clear sa sb.
induction sa0 as [ | [ta1 a1] sa1 ] => H1 H2; try clear sa0.
  rewrite occs_knit_nil_left.
  by apply is_asc_timing_coalesce.
move : ta1 a1 sa1 IHsa1 H1 H2.
induction sb0 as [ | [tb1 b1] sb1 ] => ta1 a1 sa1 IHsa1 H1 H2.
  rewrite occs_knit_nil_right.
  by apply is_asc_timing_coalesce.
rewrite occs_knit_equation.
case_eq (ta1 ?= tb1) => H3.
- apply compare_eq in H3.
  subst.
  rewrite leb_refl.
  rewrite (occs_knit_min _ _ _ _ H1 H2) => //.
  rewrite coalesce_equation.
  rewrite eqb_refl.
  move : sa1 IHsa1 H1.
  case => [ | [ta2 a2] sa2 ] IHsa1 H1.
  + rewrite occs_knit_nil_left.
    by rewrite is_asc_timing_to_coalesce_eq.
  + rewrite (@coalesce_min_le _ _ _ _ _ tb1 b1) => //.
    by apply is_asc_timing_min_coalesce_occs_knit.
- rewrite compare_lt_iff in H3.
  move : (H3) => H3'.
  apply lt_le_incl in H3'.
  rewrite -leb_le in H3'.
  rewrite H3'.
  have : is_asc_timing (coalesce f (occs_knit (sa1, (tb1, b1) :: sb1))) = true => [ | H4 ].
  + apply IHsa1 => //.
    by apply is_asc_timing_tail in H1.
  + clear IHsb1 IHsa1 H3'.
    rewrite (@coalesce_min_lt_right _ _ _ _ _ tb1 b1) => //.
    rewrite /= H4; clear H4.
    move : (coalesce_occs_knit_exists_right f _ _ _ _ _ _ H1 H2) => [tm1] [m1] [sm1] [H4 H5].
    rewrite H4.
    rewrite Bool.andb_true_r.
    by rewrite ltb_lt.
- rewrite compare_gt_iff in H3.
  move : (H3) => H3'.
  rewrite lt_nge in H3'.
  rewrite -leb_nle in H3'.
  rewrite H3'; clear H3'.
  have : is_asc_timing (coalesce f (occs_knit ((ta1, a1) :: sa1, sb1))) = true => [ | H4 ].
  + apply IHsb1 => //.
    * move => H1' H2'.
      clear IHsa1.
      move : sa1 H1 H1'.
      induction sa1 as [ | [ta2 a2] sa2 ] => H1 H1'.
      -- rewrite occs_knit_nil_left.
         by rewrite is_asc_timing_coalesce.
      -- apply IHsb1 => // H1'' H2''.
         apply IHsa2 => //.
         clear IHsb1 IHsa2 H1' H1'' H2 H2' H2'' H3.
         move : H1 => /=.
         case sa2 => [ | [ta3 a3] sa3 ] => //.
         rewrite 3!Bool.andb_true_iff.
         move => [H4 [H5 H6]].
         split => //.
         rewrite ltb_lt.
         rewrite 2!ltb_lt in H4 H5.
         by apply (lt_trans _ _ _ H4 H5).
    * by apply is_asc_timing_tail in H2.
  + rewrite coalesce_min_lt_left => //.
    rewrite /=.
    rewrite H4.
    clear IHsb1 IHsa1 H4.
    move : (coalesce_occs_knit_exists_left f _ _ _ _ _ _ H1 H2) => [tm1] [m1] [sm1] [H4 H5].
    rewrite H4.
    rewrite Bool.andb_true_r.
    by rewrite ltb_lt.
Qed.

Lemma filter_eq a (f : a -> bool) (a0 : a) (s0 : list a) :
  List.filter f (a0 :: s0) = if f a0 then a0 :: List.filter f s0 else List.filter f s0.
Proof.
by [].
Qed.

Lemma is_asc_timing_filter a (f : a -> bool) (s : stream a) :
  is_asc_timing (occs s) = true -> is_asc_timing (occs (filter f s)) = true.
Proof.
rewrite /=.
induction (occs s) as [ | [t0 a0] s0 ] => //.
move : IHs0.
case s0 as [ | [t1 a1] s1 ] => [ _ _ /= | IH H1 ].
  by case (f a0).
rewrite filter_eq /snd.
case (f a0).
- apply is_asc_timing_head.
  + apply IH.
    by apply is_asc_timing_tail in H1.
  + move => t' a' H2.
    rewrite filter_In in H2.
    case H2 => H3 H4; clear H2.
    by apply is_asc_timing_lt with (a0 := a0) (a' := a') (s0 := (t1, a1) :: s1).
- apply IH.
  by apply is_asc_timing_tail in H1.
Qed.

Lemma is_asc_timing_occs a (s : stream a) :
  is_asc_timing (occs s) = true.
Proof.
induction s.
- rewrite /=.
  by apply proj2_sig.
- by [].
- by apply is_asc_timing_map_s.
- by apply is_asc_timing_snapshot.
- by apply is_asc_timing_merge.
- by apply is_asc_timing_filter.
Qed.

(*
(* 使いそうと思ったが意外と使わなかった補題 *)
Lemma is_asc_timing_steps_hold a (a0 : a) (s : stream a) :
  is_asc_timing (snd (steps (hold a0 s))) = true.
Admitted.

Lemma is_asc_timing_steps_map_c a b (f : a -> b) (c : cell a) :
  is_asc_timing (snd (steps (map_c f c))) = true.
Admitted.

Lemma is_asc_timing_steps_apply a b (c1 : cell (a -> b)) (c2 : cell a) :
  is_asc_timing (snd (steps (apply c1 c2))) = true.
Admitted.

Lemma is_asc_timing_steps a (c : cell a) :
  is_asc_timing (snd (steps c)) = true.
Proof.
induction c.
- by [].
- by apply is_asc_timing_steps_hold.
- by apply is_asc_timing_steps_map_c.
- by apply is_asc_timing_steps_apply.
Qed.
 *)





















