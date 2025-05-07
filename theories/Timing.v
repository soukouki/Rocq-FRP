Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List PeanoNat.
From CoqFRP Require Import FRP.

Definition timing := list time.

Definition same_timing (a b : timing) := a = b.

Theorem same_timing_reflective a : same_timing a a.
Proof. by []. Qed.

Theorem same_timing_is_transitive a b c : same_timing a b -> same_timing b c -> same_timing a c.
Proof. move => H1 H2; apply (eq_trans H1 H2). Qed.

Theorem same_timing_is_commutative a b : same_timing a b -> same_timing b a.
Proof. move => H1; symmetry; exact H1. Qed.

Definition different_timing (a b : timing) := forall t, In t a <> In t b.

(* timing(a) ⊂ timing(b) であることを示す *)
Definition subset_timing (a b : timing) := forall t, In t a -> In t b.

Theorem subset_timing_is_reflective a : subset_timing a a.
Proof. by []. Qed.

Theorem subset_timing_is_transitive a b c : subset_timing a b -> subset_timing b c -> subset_timing a c.
Proof. move => H1 H2 t H3; by apply /H2 /H1. Qed.

Definition stream_timing a (s : stream a) : timing := map fst (occs s).

Definition cell_timing a (c : cell a) : timing := map fst (snd (steps c)).

Theorem stream_timing_map_s a b (f : a -> b) (s : stream a) : stream_timing (map_s f s) = stream_timing s.
Proof.
rewrite /stream_timing /=.
induction (occs s) => //=.
by rewrite IHs0.
Qed.

Theorem stream_timing_snapshot a1 a2 a3 (f : a1 -> a2 -> a3) (s : stream a1) (c : cell a2) : stream_timing (snapshot f s c) = stream_timing s.
Proof.
rewrite /stream_timing /=.
induction (occs s) => //=.
by rewrite IHs0.
Qed.

Lemma coalesce_in_head a (f : a -> a -> a) (t1 : time) (a1 : a) (s1 : str a) : In t1 (map fst (coalesce f ((t1, a1) :: s1))).
Proof.
move : a1.
induction s1 as [ | [t2 a2] s2 ] => a1.
- rewrite 2!coalesce_equation /=.
  by left.
- rewrite coalesce_equation.
  case (t1 =? t2) => /=.
  + by apply IHs2.
  + by left.
Qed.

Lemma coalesce_in_tail a (f : a -> a -> a) (t1 : time) (a1 : a) (t : time) (s1 : str a) :
  In t (map fst s1) -> In t (map fst (coalesce f ((t1, a1) :: s1))).
Proof.
move : t a1 t1.
induction s1 as [ | [t2 a2] s2 ] => // t a1 t1 H1.
rewrite coalesce_equation.
case_eq (t1 =? t2) => H2.
- case H1 => H3.
  + rewrite /= in H3.
    rewrite Nat.eqb_eq in H2.
    subst.
    by apply coalesce_in_head.
  + by apply IHs2.
- rewrite /=.
  right.
  case H1 => H3.
  + rewrite /= in H3.
    subst.
    by apply coalesce_in_head.
  + by apply IHs2.
Qed.

Lemma occs_knit_in_left a (t : time) (s1 s2 : str a) :
  In t (map fst s1) ->
  In t (map fst (occs_knit (s1, s2))).
Proof.
move : s2.
induction s1 as [ | [t1_1 a1_1] s1_1 ] => //= s2 H1.
case s2 => [ | [t2_1 a2_1] s2_1 ].
  by rewrite occs_knit_nil_right.
case H1 => /= [ -> | H3 ]; clear H1.
- rewrite occs_knit_equation.
  case (t <=? t2_1) => /=.
  + by left.
  + right.
    induction s2_1 as [ | [t2_2 a2_2] s2_2 ].
      rewrite occs_knit_nil_right.
      by left.
    rewrite occs_knit_equation.
    case (t <=? t2_2).
    * by left.
    * rewrite /=.
      right.
      apply IHs2_2.
- rewrite occs_knit_equation.
  case (t1_1 <=? t2_1) => /=.
  + right.
    by apply IHs1_1.
  + right.
    move : t1_1 a1_1.
    induction s2_1 as [ | [t2_2 a2_2] s2_2 ] => t1_1 a1_1.
      rewrite occs_knit_nil_right.
      by right.
    rewrite occs_knit_equation.
    case (t1_1 <=? t2_2).
    * right.
      by apply IHs1_1.
    * right.
      by apply IHs2_2.
Qed.

Lemma occs_knit_in_right a (t : time) (s1 s2 : str a) :
  In t (map fst s2) ->
  In t (map fst (occs_knit (s1, s2))).
Proof.
move : s1.
induction s2 as [ | [t2_1 a2_1] s2_1 ] => //= s1 H1.
case s1 => [ | [t1_1 a1_1] s1_1 ].
  by rewrite occs_knit_nil_left.
case H1 => /= [ -> | H3 ]; clear H1.
- rewrite occs_knit_equation.
  case (t1_1 <=? t) => /=.
  + right.
    induction s1_1 as [ | [t1_2 a1_2] s1_2 ].
      rewrite occs_knit_nil_left.
      by left.
    rewrite occs_knit_equation.
    case (t1_2 <=? t) => /=.
    * right.
      by apply IHs1_2.
    * by left.
  + by left.
- rewrite occs_knit_equation.
  case (t1_1 <=? t2_1) => /=.
  + right.
    induction s1_1 as [ | [t1_2 a1_2] s1_2 ].
      rewrite occs_knit_nil_left.
      by right.
    rewrite occs_knit_equation.
    case (t1_2 <=? t2_1) => /=.
    * right.
      by apply IHs1_2.
    * right.
      by apply IHs2_1.
  + right.
    by apply IHs2_1.
Qed.

Lemma coalesce_occs_knit_gt_left a (f : a -> a -> a) (t1_1 t2_1 : time) (a1_1 a2_1 : a) (s1_1 s2_1 : str a) :
  t2_1 < t1_1 ->
  str_timing_is_asc_order ((t1_1, a1_1) :: s1_1) = true ->
  str_timing_is_asc_order ((t2_1, a2_1) :: s2_1) = true ->
  coalesce f ((t2_1, a2_1) :: occs_knit ((t1_1, a1_1) :: s1_1, s2_1)) = (t2_1, a2_1) :: coalesce f (occs_knit ((t1_1, a1_1) :: s1_1, s2_1)).
Proof.
remember (occs_knit ((t1_1, a1_1) :: s1_1, s2_1)) as s3.
move : t1_1 a1_1 s1_1 t2_1 a2_1 s2_1 Heqs3.
induction s3 as [ | [t3_1 a3_1] s3_1 ] => t1_1 a1_1 s1_1 t2_1 a2_1 s2_1 Heqs3 H1 H2 H3.
  by rewrite 2!coalesce_equation.
rewrite coalesce_equation.
suff : (t2_1 =? t3_1) = false => [ -> | ].
  by case s3_1 => [ | [t3_2 a3_2] s3_2].
clear IHs3_1.
move : Heqs3 H3.
case s2_1 => [ | [t2_2 a2_2] s2_2 ] Heqs3 H3.
- rewrite occs_knit_nil_right in Heqs3.
  inversion Heqs3; subst.
  apply Nat.lt_neq in H1.
  by rewrite Nat.eqb_neq.
- rewrite occs_knit_equation in Heqs3.
  move : Heqs3.
  case (t1_1 <=? t2_2) => Heqs3.
  + inversion Heqs3; subst.
    apply Nat.lt_neq in H1.
    by rewrite Nat.eqb_neq.
  + inversion Heqs3; subst.
    rewrite /= in H3.
    apply andb_prop in H3.
    case H3 => H4 _.
    rewrite Nat.ltb_lt in H4.
    apply Nat.lt_neq in H4.
    by rewrite -Nat.eqb_neq in H4.
Qed.

Lemma coalesce_occs_knit_gt_right a (f : a -> a -> a) (t1_1 t2_1 : time) (a1_1 a2_1 : a) (s1_1 s2_1 : str a) :
  t1_1 < t2_1 ->
  str_timing_is_asc_order ((t1_1, a1_1) :: s1_1) = true ->
  str_timing_is_asc_order ((t2_1, a2_1) :: s2_1) = true ->
  coalesce f ((t1_1, a1_1) :: occs_knit (s1_1, (t2_1, a2_1) :: s2_1)) = (t2_1, a2_1) :: coalesce f (occs_knit (s1_1, (t1_1, a1_1) :: s2_1)).
Admitted.

Theorem merge_subset_timing_left a (f : a -> a -> a) (s1 s2 : stream a) : subset_timing (stream_timing s1) (stream_timing (merge s1 s2 f)).
Proof.
rewrite /stream_timing /=.
case (occs s2) as [ | [t2_1 a2_1] s2_1 ] => [ | t' H2 ].
- rewrite occs_knit_nil_right.
  case (occs s1) as [ | [t1_1 a1_1] s1_1 ] => // t' H2.
  case H2 => [ /= -> | H3 ].
  + by apply coalesce_in_head.
  + by apply coalesce_in_tail.
- case (occs s1) as [ | [t1_1 a1_1] s1_1 ] => //.
  rewrite occs_knit_equation.
  case (t1_1 <=? t2_1).
  + case H2 => [ /= -> | H4 ].
    * by apply coalesce_in_head.
    * apply coalesce_in_tail.
      by apply occs_knit_in_left.
  + apply coalesce_in_tail.
    by apply occs_knit_in_left.
Qed.

Theorem merge_subset_timing_right a (f : a -> a -> a) (s1 s2 : stream a) : subset_timing (stream_timing s2) (stream_timing (merge s1 s2 f)).
Proof.
rewrite /stream_timing /=.
case (occs s1) as [ | [t1_1 a1_1] s1_1 ] => [ | t' H2 ].
- rewrite occs_knit_nil_left.
  case (occs s2) as [ | [t2_1 a2_1] s2_1 ] => // t' H2.
  case H2 => [ /= -> | H3 ].
  + by apply coalesce_in_head.
  + by apply coalesce_in_tail.
- case (occs s2) as [ | [t2_1 a2_1] s2_1 ] => //.
  rewrite occs_knit_equation.
  case (t1_1 <=? t2_1).
  + apply coalesce_in_tail.
    by apply occs_knit_in_right.
  + case H2 => [ /= -> | H4 ].
    * by apply coalesce_in_head.
    * apply coalesce_in_tail.
      by apply occs_knit_in_right.
Qed.

Theorem filter_subset_timing a b (f : a -> bool) (s1 : stream a) (s2 : stream b) :
  same_timing (stream_timing s1) (stream_timing s2) ->
  subset_timing (stream_timing (filter f s1)) (stream_timing s2).
Proof.
rewrite /stream_timing /same_timing /=.
move => H1 t.
rewrite -H1; clear s2 H1; rename s1 into s.
induction (occs s) as [ | [t1 a1] s1 ] => //=.
case (f a1) => /= H1.
- case H1 => H2.
  + by left.
  + right.
    by apply IHs1.
- right.
  by apply IHs1.
Qed.

Theorem cell_timing_hold a (a0 : a) (s : stream a) : cell_timing (hold a0 s) = stream_timing s.
rewrite /cell_timing /stream_timing /=.
move : (str_timing_is_asc_order_occs s).
induction (occs s) as [ | [t1 a1] s1 ] => H1 /=.
  by rewrite coalesce_equation.
move : IHs1 H1.
case s1 => [ | [t2 a2] s2 ] IHs1 H1.
  by rewrite 2!coalesce_equation.
rewrite coalesce_equation.
have : (t1 =? t2) = false => [ | -> /= ].
- apply str_timing_is_asc_order_lt with (t' := t2) (a' := a2) in H1 => //=.
  + apply Nat.lt_neq in H1.
    by rewrite Nat.eqb_neq.
  + by left.
- rewrite IHs1 => //.
  by apply str_timing_is_asc_order_tail in H1.
Qed.

Theorem cell_timing_map_c a b (f : a -> b) (c : cell a) : cell_timing (map_c f c) = cell_timing c.
Proof.
rewrite /cell_timing /=.
case (steps c) => a0 c0.
induction c0 as [ | [t1 a1] c1 ] => //=.
rewrite /= in IHc1.
by rewrite IHc1.
Qed.

Theorem apply_subset_timing_left a b (c1 : cell (a -> b)) (c2 : cell a) : subset_timing (cell_timing c1) (cell_timing (apply c1 c2)).
Proof.
Admitted.

Theorem apply_subset_timing_right a b (c1 : cell (a -> b)) (c2 : cell a) : subset_timing (cell_timing c2) (cell_timing (apply c1 c2)).
Admitted.

Theorem occs_eq_to_timing_eq a (s1 s2 : stream a) : occs s1 = occs s2 -> stream_timing s1 = stream_timing s2.
Proof. move => H1; by rewrite /stream_timing H1. Qed.

Lemma steps_knit_nil_left a b (f0 : a -> b) (a0 : a) (c : list (time * a)) :
  steps_knit f0 a0 (nil, c) = nil.
Proof.
rewrite steps_knit_equation.
case c => [ | [t1 a1] c1 ] => //.
Admitted.

Theorem cell_timing_apply_constant_right a b (acons : a) (c : cell (a -> b)) :
  cell_timing (apply c (constant acons)) = cell_timing c.
Proof.
rewrite /cell_timing /=.
case (steps c) => f0 c0.
induction c0 as [ | [t1 f1] c1 ] => //=.
  by rewrite steps_knit_equation.
rewrite /= in IHc1.
rewrite -IHc1.
Admitted.

Theorem cell_timing_apply_constant_left a b (fcons : a -> b) (c : cell a) :
  cell_timing (apply (constant fcons) c) = cell_timing c.
Admitted.












