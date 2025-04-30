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

Lemma occs_knit_in_right a (t : time) (a1_1 : a) (s1_1 s2 : str a) : In t (map fst (occs_knit (((t, a1_1) :: s1_1), s2))).
Proof.
move : t a1_1 s1_1.
induction s2 as [ | [t2_1 a2_1] s2_1 ] => t a1_1 s1_1.
- rewrite occs_knit_nil_right /=.
  by left.
- rewrite occs_knit_equation.
  case (t <=? t2_1) => /=.
  + by left.
  + right.
    by apply IHs2_1.
Qed.

Lemma occs_knit_in_left_tail a (t t1_1: time) (a1_1 : a) (s1_1 : str a) (s2 : str a) :
  In t (map fst s1_1) ->
  In t (map fst (occs_knit ((t1_1, a1_1) :: s1_1, s2))).
Proof.
move : t t1_1 a1_1 s1_1.
induction s2 as [ | [t2_1 a2_1] s2_1 ] => t t1_1 a1_1 s1_1 H1.
- rewrite occs_knit_nil_right /=.
  by right.
- move : t t1_1 a1_1 t2_1 a2_1 s2_1 IHs2_1 H1.
  induction s1_1 as [ | [t1_2 a1_2] s1_2 ] => //= t t1_1 a1_1 t2_1 a2_1 s2_1 IHs2_1 H1.
  case H1 => H2.
  + subst.
    rewrite occs_knit_equation.
    case (t1_1 <=? t2_1) => /=.
    * right.
      by apply occs_knit_in_right.
    * right.
      by apply IHs2_1.
  + rewrite occs_knit_equation.
    case (t1_1 <=? t2_1) => /=.
    * right.
      by apply IHs1_2.
    * right.
      by apply IHs2_1.
Qed.

Lemma coalesce_occs_knit_gt a (f : a -> a -> a) (t1_1 t2_1 : time) (a1_1 a2_1 : a) (s1_1 s2_1 : str a) :
  t2_1 < t1_1 ->
  str_timing_is_asc_order ((t1_1, a1_1) :: s1_1) = true ->
  str_timing_is_asc_order ((t2_1, a2_1) :: s2_1) = true ->
  coalesce f ((t2_1, a2_1) :: occs_knit ((t1_1, a1_1) :: s1_1, s2_1)) = (t2_1, a2_1) :: coalesce f (occs_knit ((t1_1, a1_1) :: s1_1, s2_1)).
Admitted.

Theorem merge_subset_timing_left a (f : a -> a -> a) (s1 s2 : stream a) : subset_timing (stream_timing s1) (stream_timing (merge s1 s2 f)).
Proof.
rewrite /stream_timing /=.
move : (str_timing_is_asc_order_occs s1) (str_timing_is_asc_order_occs s2).
induction (occs s2) as [ | [t2_1 a2_1] s2_1 ] => _ _ t.
- rewrite occs_knit_nil_right.
  move : (str_timing_is_asc_order_occs s1).
  induction (occs s1) as [ | [t1_1 a1_1] s1_1 ] => //= H1.
  case => H2.
  + subst.
    move : H1 IHs1_1.
    case s1_1 => [ | [t1_2 a1_2] s1_2 ] => H1 IHs1_1.
    * rewrite 2!coalesce_equation /=.
      by left.
    * rewrite coalesce_equation.
      apply andb_prop in H1.
      case H1 => H3 H4.
      rewrite Nat.ltb_lt in H3.
      apply Nat.lt_neq in H3.
      rewrite -Nat.eqb_neq in H3.
      rewrite H3 /=.
      by left.
  + move : H1 H2 IHs1_1.
    case s1_1 => [ | [t1_2 a1_2] s1_2 ] => H1 H2 IHs1_1.
    * by rewrite /= in H2.
    * rewrite coalesce_equation.
      apply andb_prop in H1.
      case H1 => H3 H4.
      rewrite Nat.ltb_lt in H3.
      apply Nat.lt_neq in H3.
      rewrite -Nat.eqb_neq in H3.
      rewrite H3 /=.
      right.
      by apply IHs1_1.
- move : t2_1 a2_1 s2_1 IHs2_1.
  induction (occs s1) as [ | [t1_1 a1_1] s1_1 ] => // t2_1 a2_1 s2_1 H1 H2.
  rewrite occs_knit_equation.
  case_eq (t1_1 <=? t2_1) => H3.
  + move : IHs1_1 H1 H2 H3.
    case s1_1 => [ | [t1_2 a1_2] s1_2 ] => IHs1_1 H1 H2 H3.
    * rewrite occs_knit_nil_left.
      rewrite coalesce_equation.
      rewrite Nat.leb_le in H3.
      rewrite Nat.le_lteq in H3.
      case H3 => H4.
      -- apply Nat.lt_neq in H4.
         rewrite -Nat.eqb_neq in H4.
         rewrite H4 /=.
         rewrite /= in H2.
         left.
         by case H2.
      -- rewrite -Nat.eqb_eq in H4.
         rewrite H4.
         rewrite /= in H2.
         case H2 => // ->.
         by apply coalesce_in_head.
    * move : H2.
      clear IHs1_1 H1 H3.
      rewrite /=.
      case => [ H4 | [ H4 | H4 ]].
      -- subst.
         by apply coalesce_in_head.
      -- subst.
         apply coalesce_in_tail.
         rewrite occs_knit_equation.
         case_eq (t <=? t2_1) => /= H5.
         ++ by left.
         ++ right.
            by apply occs_knit_in_right.
      -- apply coalesce_in_tail.
         by apply occs_knit_in_left_tail.
  + suff : coalesce f ((t2_1, a2_1) :: occs_knit ((t1_1, a1_1) :: s1_1, s2_1)) = (t2_1, a2_1) :: coalesce f (occs_knit ((t1_1, a1_1) :: s1_1, s2_1)) => [ -> | ].
      rewrite /=.
      right.
      apply H1.
    apply coalesce_occs_knit_gt.
    * by rewrite -Nat.leb_gt.
    * 
Qed.

Theorem merge_subset_timing_right a (f : a -> a -> a) (s1 s2 : stream a) : subset_timing (stream_timing s2) (stream_timing (merge s1 s2 f)).
Admitted.

Theorem filter_subset_timing a b (f : a -> bool) (s1 : stream a) (s2 : stream b) :
  same_timing (stream_timing s1) (stream_timing s2) ->
  subset_timing (stream_timing (filter f s1)) (stream_timing s2).
Admitted.

Theorem hold_subset_timing a (a0 : a) (s : stream a) (t : time) : subset_timing (cell_timing (hold a0 s t)) (stream_timing s).
Admitted.

Theorem cell_timing_map_c a b (f : a -> b) (c : cell a) : cell_timing (map_c f c) = cell_timing c.
Admitted.

Theorem apply_subset_timing_left a b (c1 : cell (a -> b)) (c2 : cell a) : subset_timing (cell_timing c1) (cell_timing (apply c1 c2)).
Admitted.

Theorem apply_subset_timing_right a b (c1 : cell (a -> b)) (c2 : cell a) : subset_timing (cell_timing c2) (cell_timing (apply c1 c2)).
Admitted.

Theorem occs_eq_to_timing_eq a (s1 s2 : stream a) : occs s1 = occs s2 -> stream_timing s1 = stream_timing s2.
Proof. move => H1; by rewrite /stream_timing H1. Qed.

Theorem cell_timing_apply_constant_right a b (a1 : a) (c : cell (a -> b)) :
  cell_timing (apply c (constant a1)) = cell_timing c.
Admitted.

Theorem cell_timing_apply_constant_left a b (f1 : a -> b) (c : cell a) :
  cell_timing (apply (constant f1) c) = cell_timing c.
Admitted.












