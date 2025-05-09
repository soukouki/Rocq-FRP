Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List PeanoNat.
From CoqFRP Require Import FRP OccsSteps AscTiming.

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

(* 以下はtimingに関する定理 *)

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

Theorem merge_subset_timing_right a (f : a -> a -> a) (s1 s2 : stream a) :
  subset_timing (stream_timing s2) (stream_timing (merge s1 s2 f)).
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

(* 
coalesceが結論に出てくる。
sについての帰納法を書く中で、coalesceによって、要素がまとめられることは無いことを示す必要がある。
その際に、occs関数の戻り値がis_asc_timingであることを使う必要があり、is_asc_timing_occsを使うことになる。
 *)
Theorem cell_timing_hold a (a0 : a) (s : stream a) : cell_timing (hold a0 s) = stream_timing s.
rewrite /cell_timing /stream_timing /=.
move : (is_asc_timing_occs s).
induction (occs s) as [ | [t1 a1] s1 ] => H1 /=.
  by rewrite coalesce_equation.
move : IHs1 H1.
case s1 => [ | [t2 a2] s2 ] IHs1 H1.
  by rewrite 2!coalesce_equation.
rewrite coalesce_equation.
have : (t1 =? t2) = false => [ | -> /= ].
- apply is_asc_timing_lt with (t' := t2) (a' := a2) in H1 => //=.
  + apply Nat.lt_neq in H1.
    by rewrite Nat.eqb_neq.
  + by left.
- rewrite IHs1 => //.
  by apply is_asc_timing_tail in H1.
Qed.

Theorem cell_timing_map_c a b (f : a -> b) (c : cell a) : cell_timing (map_c f c) = cell_timing c.
Proof.
rewrite /cell_timing /=.
case (steps c) => a0 c0.
induction c0 as [ | [t1 a1] c1 ] => //=.
rewrite /= in IHc1.
by rewrite IHc1.
Qed.

Theorem apply_subset_timing_left p b (cf : cell (p -> b)) (cp : cell p) : subset_timing (cell_timing cf) (cell_timing (apply cf cp)).
Proof.
rewrite /cell_timing /=.
move : (steps cf) (steps cp) => [f0 cf0] [p0 cp0]; clear cf cp.
move => t H1.
by apply steps_knit_in_left.
Qed.

Theorem apply_subset_timing_right p a (cf : cell (p -> a)) (cp : cell p) : subset_timing (cell_timing cp) (cell_timing (apply cf cp)).
rewrite /cell_timing /=.
move : (steps cf) (steps cp) => [f0 cf0] [p0 cp0]; clear cf cp.
move => t H1.
by apply steps_knit_in_right.
Qed.

Theorem occs_eq_to_timing_eq a (s1 s2 : stream a) : occs s1 = occs s2 -> stream_timing s1 = stream_timing s2.
Proof. move => H1; by rewrite /stream_timing H1. Qed.

Theorem cell_timing_apply_constant_right p a (acons : p) (c : cell (p -> a)) :
  cell_timing (apply c (constant acons)) = cell_timing c.
Proof.
rewrite /cell_timing /=.
move : (steps c) => [f0 cf0]; clear c.
induction cf0 as [ | [tf1 f1] cf1].
  by rewrite steps_knit_equation.
rewrite /= in IHcf1.
rewrite steps_knit_equation /=.
rewrite -IHcf1; clear IHcf1.
by rewrite 2!steps_knit_equation.
Qed.

Theorem cell_timing_apply_constant_left p a (fcons : p -> a) (c : cell p) :
  cell_timing (apply (constant fcons) c) = cell_timing c.
Proof.
rewrite /cell_timing /=.
move : (steps c) => [p0 cp0]; clear c.
induction cp0 as [ | [tp1 p1] cp1 ].
  by rewrite steps_knit_equation.
rewrite /= in IHcp1.
rewrite steps_knit_equation /=.
rewrite -IHcp1; clear IHcp1.
by rewrite 2!steps_knit_equation.
Qed.


















