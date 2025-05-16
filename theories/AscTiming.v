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

Lemma is_asc_timing_ignore_head_value a (s0 : str a) t0 a0 b0 :
  is_asc_timing ((t0, a0) :: s0) = true ->
  is_asc_timing ((t0, b0) :: s0) = true.
Proof.
by case s0.
Qed.

Lemma is_asc_timing_skip a t0 a0 t1 a1 (s1 : str a) :
  is_asc_timing ((t0, a0) :: (t1, a1) :: s1) = true ->
  is_asc_timing ((t0, a0) :: s1) = true.
Proof.
move => H1.
rewrite /=.
rewrite /= Bool.andb_true_iff in H1.
case H1 => H2 H3.
move : H3.
case s1 => [ | [t2 a2] s2 ] => // H3.
rewrite Bool.andb_true_iff in H3.
case H3 => H4 H5.
rewrite Bool.andb_true_iff.
split => //.
rewrite ltb_lt.
rewrite 2!ltb_lt in H2 H4.
by apply (lt_trans _ t1).
Qed.

(*
類似した補題
Lemma coalesce_min_le a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  ta0 <= tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, sb0)).

Lemma coalesce_min_lt_left a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  tb0 < ta0 ->
  coalesce f ((tb0, b0) :: occs_knit ((ta0, a0) :: sa0, sb0)) = (tb0, b0) :: coalesce f(occs_knit ((ta0, a0) :: sa0, sb0)).

結論の部分にta0を含むか含まないかの違い
 *)

Lemma coalesce_min_le a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  ta0 <= tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, sb0)).
Proof.
move => H1 H2 H3.
move : H1.
case sa0 => [ | [ta1 a1] sa1 ] => H1.
  rewrite occs_knit_nil_left.
  move : H2.
  case sb0 => [ | [tb1 b1] sb1 ] => H2.
    by rewrite coalesce_equation.
  rewrite coalesce_equation.
  suff : ta0 =? tb1 = false => [ -> // | ].
  rewrite eqb_neq.
  apply lt_neq.
  apply (le_lt_trans _ tb0) => //.
  by apply is_asc_timing_head_lt in H2.
move : H2.
case sb0 => [ | [tb1 b1] sb1 ] => H2.
  rewrite occs_knit_nil_right.
  rewrite coalesce_equation.
  suff : ta0 =? ta1 = false => [ -> // | ].
  rewrite eqb_neq.
  apply lt_neq.
  by apply is_asc_timing_head_lt in H1.
rewrite occs_knit_equation.
case (ta1 <=? tb1).
- rewrite coalesce_equation.
  suff : ta0 =? ta1 = false => [ -> // | ].
  apply is_asc_timing_head_lt in H1.
  rewrite eqb_neq.
  by apply lt_neq.
- rewrite coalesce_equation.
  suff : ta0 =? tb1 = false => [ -> // | ].
  rewrite eqb_neq.
  apply lt_neq.
  apply (le_lt_trans _ tb0) => //.
  by apply is_asc_timing_head_lt in H2.
Qed.

Lemma coalesce_min_lt_right a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  ta0 < tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, (tb0, b0) :: sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, (tb0, b0) :: sb0)).
Proof.
move => H1 H2 H3.
move : H1.
case sa0 => [ | [ta1 a1] sa1 ] => H1.
  rewrite occs_knit_nil_left.
  rewrite coalesce_equation.
  suff : ta0 =? tb0 = false => [ -> // | ].
  rewrite eqb_neq.
  by apply lt_neq.
rewrite occs_knit_equation.
case (ta1 <=? tb0).
- rewrite coalesce_equation.
  suff : ta0 =? ta1 = false => [ -> // | ].
  rewrite eqb_neq.
  apply lt_neq.
  by apply is_asc_timing_head_lt in H1.
- rewrite coalesce_equation.
  suff : ta0 =? tb0 = false => [ -> // | ].
  rewrite eqb_neq.
  by apply lt_neq.
Qed.

Lemma coalesce_min_lt_left a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  is_asc_timing ((ta0, a0) :: sa0) = true ->
  is_asc_timing ((tb0, b0) :: sb0) = true ->
  tb0 < ta0 ->
  coalesce f ((tb0, b0) :: occs_knit ((ta0, a0) :: sa0, sb0)) = (tb0, b0) :: coalesce f(occs_knit ((ta0, a0) :: sa0, sb0)).
Proof.
move => H1 H2 H3.
move : H2.
case sb0 => [ | [tb1 b1] sb1 ] => H2.
  rewrite occs_knit_nil_right.
  rewrite coalesce_equation.
  suff : tb0 =? ta0 = false => [ -> // | ].
  rewrite eqb_neq.
  by apply lt_neq.
rewrite occs_knit_equation.
case (ta0 <=? tb1).
- rewrite coalesce_equation.
  suff : tb0 =? ta0 = false => [ -> // | ].
  rewrite eqb_neq.
  by apply lt_neq.
- rewrite coalesce_equation.
  suff : tb0 =? tb1 = false => [ -> // | ].
  rewrite eqb_neq.
  apply lt_neq.
  by apply is_asc_timing_head_lt in H2.
Qed.

Lemma occs_knit_min a t0 a0 sa0 (b0 : a) sb0 :
  is_asc_timing ((t0, a0) :: sa0) = true ->
  is_asc_timing ((t0, b0) :: sb0) = true ->
  occs_knit (sa0, (t0, b0) :: sb0) = (t0, b0) :: occs_knit (sa0, sb0).
Proof.
move : sa0 t0 a0 b0 sb0.
induction sa0 as [ | [ta1 a1] sa1 ] => t0 a0 b0 sb0 H1 H2.
  by rewrite 2!occs_knit_nil_left.
rewrite occs_knit_equation.
suff : ta1 <=? t0 = false => [ -> // | ].
apply is_asc_timing_head_lt in H1.
by rewrite leb_nle -lt_nge.
Qed.

Lemma coalesce_occs_knit_exists_left a (f : a -> a -> a) (ta1 tb1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  is_asc_timing ((ta1, a1) :: sa1) = true ->
  is_asc_timing ((tb1, b1) :: sb1) = true ->
  tb1 < ta1 ->
  exists tm1 m1 sm1,
    coalesce f (occs_knit ((ta1, a1) :: sa1, sb1)) = (tm1, m1) :: sm1 /\ tb1 < tm1.
Proof.
move => H1 H2 H3.
move : H2.
case sb1 => [ | [tb2 b2] sb2 ] => H2.
  rewrite occs_knit_nil_right.
  move : (coalesce_exists_head f ta1 a1 sa1) => [m1] [sm1] ->.
  exists ta1.
  exists m1.
  by exists sm1.
move : (@occs_knit_exists a tb1 ta1 tb2 a1 b2 sa1 sb2) => [ // | | tm1 [m1] [sm1] [-> H5] ].
  by apply is_asc_timing_head_lt in H2.
move : (coalesce_exists_head f tm1 m1 sm1) => [m1'] [sm1'] ->.
exists tm1.
exists m1'.
by exists sm1'.
Qed.

Lemma coalesce_occs_knit_exists_right a (f : a -> a -> a) (ta1 tb1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  is_asc_timing ((ta1, a1) :: sa1) = true ->
  is_asc_timing ((tb1, b1) :: sb1) = true ->
  ta1 < tb1 ->
  exists tm1 m1 sm1,
    coalesce f (occs_knit (sa1, (tb1, b1) :: sb1)) = (tm1, m1) :: sm1 /\ ta1 < tm1.
Proof.
move => H1 H2 H3.
move : H1.
case sa1 => [ | [ta2 a2] sa2 ] => H1.
  rewrite occs_knit_nil_left.
  move : (coalesce_exists_head f tb1 b1 sb1) => [m1] [sm1] ->.
  exists tb1.
  exists m1.
  by exists sm1.
move : (@occs_knit_exists a ta1 ta2 tb1 a2 b1 sa2 sb1) => [ | // | tm1 [m1] [sm1] [-> H5] ].
  by apply is_asc_timing_head_lt in H1.
move : (coalesce_exists_head f tm1 m1 sm1) => [m1'] [sm1'] ->.
exists tm1.
exists m1'.
by exists sm1'.
Qed.

Lemma coalesce_occs_knit_or a (f : a -> a -> a) (t1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  is_asc_timing ((t1, a1) :: sa1) = true ->
  is_asc_timing ((t1, b1) :: sb1) = true ->
  coalesce f (occs_knit (sa1, sb1)) = nil \/ exists tm1 m1 sm1, coalesce f (occs_knit (sa1, sb1)) = (tm1, m1) :: sm1 /\ t1 < tm1.
Proof.
case sa1 => [ | [ta2 a2] sa2 ];
case sb1 => [ | [tb2 b2] sb2 ] => H1 H2.
- left.
  by rewrite occs_knit_equation coalesce_equation.
- right.
  rewrite occs_knit_nil_left.
  move : (coalesce_exists_head f tb2 b2 sb2) => [m1] [sm1] ->.
  exists tb2.
  exists m1.
  exists sm1.
  split => //.
  by apply is_asc_timing_head_lt in H2.
- right.
  rewrite occs_knit_nil_right.
  move : (coalesce_exists_head f ta2 a2 sa2) => [m1] [sm1] ->.
  exists ta2.
  exists m1.
  exists sm1.
  split => //.
  by apply is_asc_timing_head_lt in H1.
- right.
  rewrite occs_knit_equation.
  case (ta2 <=? tb2).
  + move : (coalesce_exists_head f ta2 a2 (occs_knit (sa2, (tb2, b2) :: sb2))) => [m1] [sm1] ->.
    exists ta2.
    exists m1.
    exists sm1.
    split => //.
    by apply is_asc_timing_head_lt in H1.
  + move : (coalesce_exists_head f tb2 b2 (occs_knit ((ta2, a2) :: sa2, sb2))) => [m1] [sm1] ->.
    exists tb2.
    exists m1.
    exists sm1.
    split => //.
    by apply is_asc_timing_head_lt in H2.
Qed.

Lemma double_induction_list a b (P : list a -> list b -> Prop) :
  (forall sa, P sa []) ->
  (forall sb, P [] sb) ->
  (forall sa1 sb1,
    (forall a1, P (a1 :: sa1) sb1) ->
    (forall b1, P sa1 (b1 :: sb1)) ->
    P sa1 sb1 ->
    forall a1 b1, P (a1 :: sa1) (b1 :: sb1)
  ) ->
  forall sa sb, P sa sb.
Proof.
move => H1 H2 H3.
induction sa as [ | a1 sa1 ] => // sb.
move : a1 sa1 IHsa1.
induction sb as [ | b1 sb1 ] => // a1 sa1 IHsa1.
apply H3 => // a0.
by apply IHsb1.
Qed.

Lemma is_asc_timing_merge a (sa sb : stream a) (f : a -> a -> a) :
  is_asc_timing (occs sa) = true ->
  is_asc_timing (occs sb) = true ->
  is_asc_timing (occs (merge sa sb f)) = true.
Proof.
rewrite /=.
move : (occs sa) (occs sb) => sa0 sb0; clear sa sb.
apply (double_induction_list (fun sa' sb' => is_asc_timing sa' = true -> is_asc_timing sb' = true -> is_asc_timing (coalesce f (occs_knit (sa', sb'))) = true)).
- move => sa H1 H2.
  rewrite occs_knit_nil_right.
  by apply is_asc_timing_coalesce.
- move => sb H1 H2.
  rewrite occs_knit_nil_left.
  by apply is_asc_timing_coalesce.
- move => sa1 sb1 H1 H2 H3 [ta1 a1] [tb1 b1] H4 H5.
  case_eq (ta1 ?= tb1) => H6.
  + rewrite compare_eq_iff in H6.
    subst.
    rewrite occs_knit_equation.
    rewrite leb_refl.
    rewrite (occs_knit_min _ _ _ _ _ H4 H5) => //.
    rewrite coalesce_equation.
    rewrite eqb_refl.
    rewrite (@coalesce_min_le _ f _ _ _ tb1 b1) => //.
    have : is_asc_timing (coalesce f (occs_knit (sa1, sb1))) = true => [ | H6 ].
      apply H3; by [ apply is_asc_timing_tail in H4 | apply is_asc_timing_tail in H5 ].
    rewrite /= H6.
    move : (coalesce_occs_knit_or f _ _ _ _ _ H4 H5).
    case => [ -> // | H7 ].
    move : H7 => [tm1] [m1] [sm1] [H8 H9].
    rewrite H8.
    rewrite Bool.andb_true_r.
    by rewrite ltb_lt.
  + rewrite compare_lt_iff in H6.
    rewrite occs_knit_equation.
    have : ta1 <=? tb1 = true => [ | -> ].
      rewrite leb_le.
      by apply lt_le_incl.
    rewrite (@coalesce_min_lt_right _ _ _ _ _ tb1 b1) => //.
    have : is_asc_timing (coalesce f (occs_knit (sa1, (tb1, b1) :: sb1))) = true => [ | H7 ].
      apply H2 => //.
      by apply is_asc_timing_tail in H4.
    rewrite /= H7.
    move : (coalesce_occs_knit_exists_right f _ _ _ _ H4 H5 H6) => [tm1] [m1] [sm1] [H8 H9].
    rewrite H8.
    rewrite Bool.andb_true_r.
    by rewrite ltb_lt.
  + rewrite compare_gt_iff in H6.
    rewrite occs_knit_equation.
    have : ta1 <=? tb1 = false => [ | -> ].
      by rewrite leb_gt.
    rewrite (@coalesce_min_lt_left _ _ _ _ _ tb1 b1) => //.
    have : is_asc_timing (coalesce f (occs_knit ((ta1, a1) :: sa1, sb1))) = true => [ | H7 ].
      apply H1 => //.
      by apply is_asc_timing_tail in H5.
    rewrite /= H7.
    move : (coalesce_occs_knit_exists_left f _ _ _ _ H4 H5 H6) => [tm1] [m1] [sm1] [H8 H9].
    rewrite H8.
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
Lemma is_asc_timing_hold a (a0 : a) (s : stream a) :
  is_asc_timing (snd (steps (hold a0 s))) = true.
Admitted.

Lemma is_asc_timing_map_c a b (f : a -> b) (c : cell a) :
  is_asc_timing (snd (steps (map_c f c))) = true.
Admitted.

Lemma is_asc_timing_apply a b (c1 : cell (a -> b)) (c2 : cell a) :
  is_asc_timing (snd (steps (apply c1 c2))) = true.
Admitted.

Lemma is_asc_timing_steps a (c : cell a) :
  is_asc_timing (snd (steps c)) = true.
Proof.
induction c.
- by [].
- by apply is_asc_timing_hold.
- by apply is_asc_timing_map_c.
- by apply is_asc_timing_apply.
Qed.
 *)





















