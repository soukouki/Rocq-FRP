
Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
Import ListNotations.
Import Peano PeanoNat.Nat.

(* splitプリミティブを実装しないため、論理的時刻はnatで十分 *)
Definition time := nat.

Definition str a := list (time * a).
Definition cel a := (a * (list (time * a)))%type.

Fixpoint str_timing_is_asc_order a (s : str a) : bool :=
  match s with
  | nil => true
  | (t1, a1) :: nil => true
  | (t1, a1) :: ((t2, a2) :: _) as tas => (t1 <? t2) && str_timing_is_asc_order tas
  end.

(* 本来は更にプリミティブが何種類かあるが、今回証明するモデルでは省略する *)
Inductive stream a :=
  | mk_stream : { s : str a | str_timing_is_asc_order s = true } -> stream a
  | never : stream a
  | map_s prev : (prev -> a) -> stream prev -> stream a
  | snapshot prev_s prev_c : (prev_s -> prev_c -> a) -> stream prev_s -> cell prev_c -> stream a
  | merge : stream a -> stream a -> (a -> a -> a) -> stream a
  | filter : (a -> bool) -> stream a -> stream a
with cell a :=
  | constant : a -> cell a
  | hold : a -> stream a (* -> time *) -> cell a (* Sodiumの意味論ではholdはTを受け取るが、今回実装するモデルではここに0が入るとする *)
  | map_c prev : (prev -> a) -> cell prev -> cell a
  | apply prev : cell (prev -> a) -> cell prev -> cell a.

Definition at_ a (cel : cel a) (t : time) : a :=
  last (map snd (List.filter (fun ta => (fst ta) <? t) (snd cel))) (fst cel).

(* リストを前から見ていき、前2つが同じ時刻であれば、関数fでまとめたリストを返す *)
Function coalesce a (f : a -> a -> a) (s : str a) {measure length s} : str a :=
  match s with
  | (t1, a1) :: ((t2, a2) :: tas2) as tas1 =>
    if t1 =? t2
    then
      coalesce f ((t1, f a1 a2) :: tas2)
    else
      (t1, a1) :: coalesce f tas1
  | ta1 :: tas => ta1 :: coalesce f tas
  | [] => []
  end.
Proof.
- by auto.
- by auto.
- by auto.
Qed.

Function occs_knit a (ab : (str a * str a)) {measure (fun (ab : str a * str a) => length (fst ab) + length (snd ab)) ab} :=
  match ab with
  | (((ta, a) :: tas2) as tas1,  ((tb, b) :: tbs2) as tbs1) =>
    if ta <=? tb
    then
      (ta, a) :: occs_knit (tas2, tbs1)
    else
      (tb, b) :: occs_knit (tas1, tbs2)
  | (tas, tbs) => tas ++ tbs
  end.
Proof.
- by auto.
- move => a ab tas tbs p tas2 ta a0 H1 H2 p0 tbs2 tb b H3 H4 H5 H6.
  rewrite /=.
  rewrite -succ_lt_mono.
  by apply add_lt_mono_l.
Qed.

Function steps_knit p a (f0 : p -> a) (p0 : p) (fps : (list (time * (p -> a)) * list (time * p)))
  {measure (fun fps => length (fst fps) + length (snd fps)) fps}
  : list (time * a) :=
  match fps with
  | (((ft1, f1) :: fs1) as fs, ((pt1, p1) :: ps1) as ps) =>
    match ft1 ?= pt1 with
    | Lt => steps_knit f1 p0 (fs1, ps)
    | Gt => steps_knit f0 p1 (fs, ps1)
    | Eq => steps_knit f1 p1 (fs1, ps1)
    end
  | ((ft1, f1) :: fs1, []) => steps_knit f1 p0 (fs1, [])
  | ([], (pt1, p1) :: ps1) => steps_knit f0 p1 ([], ps1)
  | ([], []) => []
  end.
Proof.
- by auto.
- by auto.
- move => p a f0 p0 fps fs ps ft1f1 fs1 ft1 f1 H1 H2 pt1p1 ps1 pt1 p1 H3 H4 H5 H6.
  rewrite /= add_succ_r.
  by apply le_S.
- by auto.
- move => p a f0 p0 fps fs ps ft1f1 fs1 ft1 f1 H1 H2 pt1p1 ps1 pt1 p1 H3 H4 H5 H6.
  by rewrite /= add_succ_r.
Qed.

Fixpoint occs a (s_ : stream a) : str a :=
  match s_ with
  | mk_stream s => proj1_sig s
  | never _ => []
  | map_s f s => map (fun ta => (fst ta, f (snd ta))) (occs s)
  | snapshot f s c => map (fun ta => (fst ta, f (snd ta) (at_ (steps c) (fst ta)))) (occs s)
  | merge sa sb f => coalesce f (occs_knit (occs sa, occs sb))
  | filter pred s => List.filter (fun ta => pred (snd ta)) (occs s)
  end
with steps a (c_ : cell a) : cel a :=
  match c_ with
  | constant a => (a, [])
  | hold a s => (a, coalesce (fun x y => y) (occs s))
  | map_c f c =>
    let stp := steps c in
    (f (fst stp), map (fun ta => (fst ta, f (snd ta))) (snd stp))
  | apply cf cp =>
    let (f, fsts) := steps cf in
    let (p, psts) := steps cp in
    (f p, steps_knit f p (fsts, psts))
  end.

Theorem occs_map_never a b (f : a -> b) : occs (map_s f (never a)) = occs (never b).
Proof. by []. Qed.

Lemma str_timing_is_asc_order_tail a (tp1 : time * a) tps1 :
  str_timing_is_asc_order (tp1 :: tps1) = true -> str_timing_is_asc_order tps1 = true.
Proof.
case tp1 => t1 a1.
case tps1 => // tp2 tps2; clear tps1.
case tp2 => t2 a2.
rewrite /= => H1.
rewrite Bool.andb_true_iff in H1.
by case H1.
Qed.

Lemma str_timing_is_asc_order_head a t0 a0 (s0 : str a) :
  str_timing_is_asc_order s0 = true ->
  (forall t' a', In (t', a') s0 -> t0 < t') ->
  str_timing_is_asc_order ((t0, a0) :: s0) = true.
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

Lemma str_timing_is_asc_order_head_lt a t0 a0 t1 a1 (s1 : str a) :
  str_timing_is_asc_order ((t0, a0) :: (t1, a1) :: s1) = true ->
  t0 < t1.
Proof.
rewrite /str_timing_is_asc_order.
rewrite Bool.andb_true_iff.
case => H1 _.
by apply ltb_lt in H1.
Qed.

Lemma str_timing_is_asc_order_lt a t0 a0 (s0 : str a) :
  str_timing_is_asc_order ((t0, a0) :: s0) = true ->
  forall t' a', In (t', a') s0 -> t0 < t'.
Proof.
move : t0 a0.
induction s0 as [ | [t1 a1] s1 ] => //.
move => t0 a0 H1 t' a' /= H2.
case H2 => H3.
- inversion H3.
  subst; clear H2 H3.
  by apply str_timing_is_asc_order_head_lt in H1.
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

Lemma str_timing_is_asc_order_first_lt a (ta1 ta2 : time * a) tas2 :
  str_timing_is_asc_order (ta1 :: ta2 :: tas2) = true -> fst ta1 <? fst ta2 = true.
Proof.
case ta1 => t1 a1.
case ta2 => t2 a2.
rewrite /= => H1.
rewrite Bool.andb_true_iff in H1.
by case H1.
Qed.

Lemma str_timing_is_asc_order_iff a t0 a0 (s0 : str a) :
  str_timing_is_asc_order s0 = true /\ (forall t' a', In (t', a') s0 -> t0 < t') <->
  str_timing_is_asc_order ((t0, a0) :: s0) = true.
Proof.
split => [ [H1 H2] | H1 ].
- apply str_timing_is_asc_order_head => // t'.
- split.
  + by apply str_timing_is_asc_order_tail in H1.
  + by apply str_timing_is_asc_order_lt with (a0 := a0).
Qed.

Lemma str_timing_is_asc_order_map_s p a (f : p -> a) (s : stream p) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (map_s f s)) = true.
Proof.
rewrite /=.
move : (occs s) => tas0 H1.
induction tas0 as [ | ta1 tas1 IH ] => //=.
rewrite IH; clear IH.
- by apply str_timing_is_asc_order_tail in H1.
- move : tas1 H1.
  case => // ta2 tas2 H1.
  rewrite /=.
  rewrite Bool.andb_true_iff.
  split => //.
  by apply str_timing_is_asc_order_first_lt in H1.
Qed.

Lemma str_timing_is_asc_order_snapshot a prev_s prev_c (f : prev_s -> prev_c -> a) (s : stream prev_s) (c : cell prev_c) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (snapshot f s c)) = true.
Proof.
rewrite /=.
move : (occs s) => tas0 H1.
induction tas0 as [ | ta1 tas1 IH ] => //=.
rewrite IH; clear IH.
- by apply str_timing_is_asc_order_tail in H1.
- move: tas1 H1.
  case => // ta2 tas2 H1.
  rewrite /=.
  rewrite Bool.andb_true_iff.
  split => //.
  by apply str_timing_is_asc_order_first_lt in H1.
Qed.

Lemma str_timing_is_asc_order_ignore_head_value a (s0 : str a) t0 a0 b0 :
  str_timing_is_asc_order ((t0, a0) :: s0) = true ->
  str_timing_is_asc_order ((t0, b0) :: s0) = true.
Proof.
by case s0.
Qed.

Lemma str_timing_is_asc_order_to_coalesce_eq a (s : str a) (f : a -> a -> a) :
  str_timing_is_asc_order s = true -> coalesce f s = s.
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
  apply (str_timing_is_asc_order_lt _ _ _ H1 _ a2).
  by left.
rewrite IHs1 => //.
by apply str_timing_is_asc_order_tail in H1.
Qed.

Lemma str_timing_is_asc_order_coalesce a (s : str a) (f : a -> a -> a) :
  str_timing_is_asc_order s = true -> str_timing_is_asc_order (coalesce f s) = true.
Proof.
move => H1.
by rewrite str_timing_is_asc_order_to_coalesce_eq.
Qed.

Lemma str_timing_is_asc_order_coalesce_ignore_head_value a (s0 : str a) (f : a -> a -> a) t0 a0 b0 :
  str_timing_is_asc_order (coalesce f ((t0, a0) :: s0)) = true ->
  str_timing_is_asc_order (coalesce f ((t0, b0) :: s0)) = true.
Proof.
move : t0 a0 b0.
induction s0 as [ | [t1 a1] s1 ] => t0 a0 b0 H1.
  by rewrite 2!coalesce_equation.
rewrite coalesce_equation.
case (t0 =? t1).
- apply IHs1 with (a0 := a0); clear IHs1 b0.
  move : t0 a0 t1 a1 H1.
  induction s1 as [ | [t2 a2] s2 ] => t0 a0 t1 a1 H1.
    by rewrite 2!coalesce_equation.
Admitted.

Lemma coalesce_min_le a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  str_timing_is_asc_order ((ta0, a0) :: sa0) = true ->
  str_timing_is_asc_order ((tb0, b0) :: sb0) = true ->
  ta0 <= tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, sb0)).
Proof.
Admitted.

Lemma coalesce_min_lt_right a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  str_timing_is_asc_order ((ta0, a0) :: sa0) = true ->
  str_timing_is_asc_order ((tb0, b0) :: sb0) = true ->
  ta0 < tb0 ->
  coalesce f ((ta0, a0) :: occs_knit (sa0, (tb0, b0) :: sb0)) = (ta0, a0) :: coalesce f(occs_knit (sa0, (tb0, b0) :: sb0)).
Proof.
Admitted.

Lemma coalesce_min_lt_left a (f : a -> a -> a) ta0 a0 sa0 tb0 b0 sb0 :
  str_timing_is_asc_order ((ta0, a0) :: sa0) = true ->
  str_timing_is_asc_order ((tb0, b0) :: sb0) = true ->
  tb0 < ta0 ->
  coalesce f ((tb0, b0) :: occs_knit ((ta0, a0) :: sa0, sb0)) = (ta0, a0) :: coalesce f(occs_knit ((ta0, a0) :: sa0, sb0)).
Proof.
Admitted.

Lemma occs_knit_min a ta0 a0 sa0 tb0 (b0 : a) sb0 :
  str_timing_is_asc_order ((ta0, a0) :: sa0) = true ->
  str_timing_is_asc_order ((tb0, b0) :: sb0) = true ->
  ta0 <= tb0 ->
  occs_knit (sa0, (tb0, b0) :: sb0) = (tb0, b0) :: occs_knit (sa0, sb0).
Proof.
Admitted.

Lemma str_timing_is_asc_order_occs_knit a (f : a -> a -> a) t0 a0 sa b0 sb :
  str_timing_is_asc_order ((t0, a0) :: sa) = true ->
  str_timing_is_asc_order ((t0, b0) :: sb) = true ->
  str_timing_is_asc_order ((t0, f a0 b0) :: coalesce f (occs_knit (sa, sb))) = true.
Proof.
Admitted.

Lemma str_timing_is_asc_order_coalesce_in a (f : a -> a -> a) s t' a' :
  str_timing_is_asc_order s = true ->
  In (t', a') (coalesce f s) <-> In (t', a') s.
Proof.
Admitted.

Lemma occs_knit_nil_right a (s : str a) : occs_knit (s, []) = s.
Proof.
rewrite occs_knit_equation.
rewrite app_nil_r.
by case s => // [[t1 a1] s1].
Qed.

Lemma occs_knit_nil_left a (s : str a) : occs_knit ([], s) = s.
Proof.
by rewrite occs_knit_equation.
Qed.

Lemma str_timing_is_asc_order_eq a (t1 t2 : time) (a1 a2 : a) (s2 : str a) :
  str_timing_is_asc_order ((t1, a1) :: (t2, a2) :: s2) = true <-> ((t1 <? t2) && str_timing_is_asc_order ((t2, a2) :: s2))%bool = true.
Proof. by []. Qed.

Lemma str_timing_is_asc_order_min_coalesce_occs_knit a (f : a -> a -> a) (t1 ta2 : time) (a1 a2 b1 : a) (sa2 sb1 : str a) :
  str_timing_is_asc_order ((t1, a1) :: (ta2, a2) :: sa2) = true ->
  str_timing_is_asc_order ((t1, b1) :: sb1) = true ->
  str_timing_is_asc_order ((t1, f a1 b1) :: coalesce f (occs_knit ((ta2, a2) :: sa2, sb1))) = true.
Proof.
Admitted.

Lemma coalesce_occs_knit_exists_right a (f : a -> a -> a) (ta1 tb1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  str_timing_is_asc_order ((ta1, a1) :: sa1) = true ->
  str_timing_is_asc_order ((tb1, b1) :: sb1) = true ->
  exists tm1 m1 sm1,
    coalesce f (occs_knit (sa1, (tb1, b1) :: sb1)) = (tm1, m1) :: sm1 /\ ta1 < tm1.
Admitted.

Lemma coalesce_occs_knit_exists_left a (f : a -> a -> a) (ta1 tb1 : time) (a1 b1 : a) (sa1 sb1 : str a) :
  str_timing_is_asc_order ((ta1, a1) :: sa1) = true ->
  str_timing_is_asc_order ((tb1, b1) :: sb1) = true ->
  exists tm1 m1 sm1,
    coalesce f (occs_knit ((ta1, a1) :: sa1, sb1)) = (tm1, m1) :: sm1 /\ ta1 < tm1.
Admitted.

Lemma str_timing_is_asc_order_merge a (sa sb : stream a) (f : a -> a -> a) :
  str_timing_is_asc_order (occs sa) = true ->
  str_timing_is_asc_order (occs sb) = true ->
  str_timing_is_asc_order (occs (merge sa sb f)) = true.
Proof.
move => H1 H2 /=.
move : (occs sb) H2; clear sb; move => sb.
move : H1 sb.
induction (occs sa) as [ | [ta0 a0] sa0 ] => [ _ sb H2 | H4 ].
- rewrite occs_knit_equation.
  rewrite app_nil_l.
  move : H2.
  induction sb as [ | [tb0 b0] sb0 ].
  + by rewrite coalesce_equation.
  + move : IHsb0.
    case sb0 => [ | [tb1 b1] sb1 IHsb0 H2 ].
      by rewrite 3!coalesce_equation.
    rewrite coalesce_equation.
    case_eq (tb0 =? tb1) => [ H3 | _ ].
    * rewrite eqb_eq in H3.
      subst.
      rewrite (str_timing_is_asc_order_coalesce_ignore_head_value _ _ _ b1) => //.
      apply IHsb0.
      by apply str_timing_is_asc_order_tail in H2.
    * apply str_timing_is_asc_order_head.
      -- rewrite IHsb0 => //.
         by apply str_timing_is_asc_order_tail in H2.
      -- move => t' a' H3.
         move : (str_timing_is_asc_order_lt _ _ _ H2 t' a').
         apply.
         rewrite str_timing_is_asc_order_coalesce_in in H3 => //.
         by apply str_timing_is_asc_order_tail in H2.
- case => [ _ | [tb0 b0] sb0 H5 ].
  + rewrite occs_knit_equation.
    rewrite app_nil_r.
    by apply str_timing_is_asc_order_coalesce.
  + rewrite occs_knit_equation.
    case_eq (ta0 ?= tb0) => H6.
    * apply compare_eq in H6.
      subst.
      rewrite leb_refl.
      rewrite (occs_knit_min a0 _ _ _ _ _ (le_refl tb0)) => //.
      rewrite coalesce_equation.
      rewrite eqb_refl.
      rewrite (coalesce_min_le _ _ _ _ _ _ H5).
      -- by apply str_timing_is_asc_order_ignore_head_value with (a0 := a0).
      -- by apply le_refl.
      -- by apply str_timing_is_asc_order_occs_knit.
    * rewrite compare_lt_iff in H6.
      move : (lt_le_incl _ _ H6) => H7.
      move : (iffRL (leb_le ta0 tb0) H7) => H8.
      rewrite H8.
      rewrite (occs_knit_min a0 _ _ _ _ _ H7) => //.
      rewrite coalesce_equation.
      move : (lt_neq _ _ H6) => H9.
      rewrite -eqb_neq in H9.
      rewrite H9.
      rewrite -(occs_knit_min a0 _ _ _ _ _ H7) => //.
      apply str_timing_is_asc_order_head => [ | t' a' H10 ].
      -- apply IHsa0 => //.
         by apply str_timing_is_asc_order_tail in H4.
      -- rewrite str_timing_is_asc_order_coalesce_in in H10.
         ++ rewrite (occs_knit_min a0 _ _ _ _ _ H7) => //.
            apply str_timing_is_asc_order_head.
            ** admit.
            ** admit.
         ++ admit.
    * admit.
Restart.
rewrite /=.
induction (occs sa) as [ | [ta1 a1] sa1 ] => [ _ H2 | H1 H2 ]; clear sa.
  rewrite occs_knit_nil_left.
  by apply str_timing_is_asc_order_coalesce.
move : ta1 a1 sa1 IHsa1 H1 H2.
induction (occs sb) as [ | [tb1 b1] sb1 ] => ta1 a1 sa1 IHsa1 H1 H2; clear sb.
  rewrite occs_knit_nil_right.
  by apply str_timing_is_asc_order_coalesce.
rewrite occs_knit_equation.
case_eq (ta1 ?= tb1) => H3.
- apply compare_eq in H3.
  subst.
  rewrite leb_refl.
  have : occs_knit (sa1, (tb1, b1) :: sb1) = (tb1, b1) :: occs_knit (sa1, sb1) => [ | -> ].
  + clear IHsa1 IHsb1.
    move : H1.
    case sa1 => [ H1 | [ta2 a2] sa2 H1 ].
    * by rewrite 2!occs_knit_nil_left.
    * rewrite occs_knit_equation.
      case_eq (ta2 <=? tb1) => H3 //.
      exfalso.
      rewrite /= in H1.
      apply andb_prop in H1.
      case H1 => H1' _; clear H1.
      rewrite leb_le in H3.
      rewrite ltb_lt in H1'.
      by rewrite -nlt_ge in H3.
  + rewrite coalesce_equation.
    rewrite eqb_refl.
    rewrite (@coalesce_min_le a f tb1 (f a1 b1) sa1 tb1 b1 sb1) => //.
    move : IHsa1 H1 H2.
    case sa1 => [ | [ta2 a2] sa2 ] IHsa1 H1 H2.
    * rewrite occs_knit_nil_left.
      rewrite occs_knit_nil_left in IHsa1.
Restart.
rewrite /=.
move : (occs sa) (occs sb) => sa0 sb0; clear sa sb.
induction sa0 as [ | [ta1 a1] sa1 ] => H1 H2; try clear sa0.
  rewrite occs_knit_nil_left.
  by apply str_timing_is_asc_order_coalesce.
move : ta1 a1 sa1 IHsa1 H1 H2.
induction sb0 as [ | [tb1 b1] sb1 ] => ta1 a1 sa1 IHsa1 H1 H2.
  rewrite occs_knit_nil_right.
  by apply str_timing_is_asc_order_coalesce.
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
    by rewrite str_timing_is_asc_order_to_coalesce_eq.
  + rewrite (@coalesce_min_le _ _ _ _ _ tb1 b1) => //.
    by apply str_timing_is_asc_order_min_coalesce_occs_knit.
- rewrite compare_lt_iff in H3.
  move : (H3) => H3'.
  apply lt_le_incl in H3'.
  rewrite -leb_le in H3'.
  rewrite H3'.
  have : str_timing_is_asc_order (coalesce f (occs_knit (sa1, (tb1, b1) :: sb1))) = true => [ | H4 ].
  + apply IHsa1 => //.
    by apply str_timing_is_asc_order_tail in H1.
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
  have : str_timing_is_asc_order (coalesce f (occs_knit ((ta1, a1) :: sa1, sb1))) = true => [ | H4 ].
  + apply IHsb1 => //.
    * move => H1' H2'.
      clear IHsa1.
      move : sa1 H1 H1'.
      induction sa1 as [ | [ta2 a2] sa2 ] => H1 H1'.
      -- rewrite occs_knit_nil_left.
         by rewrite str_timing_is_asc_order_coalesce.
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
    * by apply str_timing_is_asc_order_tail in H2.
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

Lemma str_timing_is_asc_order_filter a (f : a -> bool) (s : stream a) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (filter f s)) = true.
Proof.
rewrite /=.
induction (occs s) as [ | [t0 a0] s0 ] => //.
move : IHs0.
case s0 as [ | [t1 a1] s1 ] => [ _ _ /= | IH H1 ].
  by case (f a0).
rewrite filter_eq /snd.
case (f a0).
- apply str_timing_is_asc_order_head.
  + apply IH.
    by apply str_timing_is_asc_order_tail in H1.
  + move => t' a' H2.
    rewrite filter_In in H2.
    case H2 => H3 H4; clear H2.
    by apply str_timing_is_asc_order_lt with (a0 := a0) (a' := a') (s0 := (t1, a1) :: s1).
- apply IH.
  by apply str_timing_is_asc_order_tail in H1.
Qed.

Theorem str_timing_is_asc_order_occs a (s : stream a) :
  str_timing_is_asc_order (occs s) = true.
Proof.
induction s.
- rewrite /=.
  by apply proj2_sig.
- by [].
- by apply str_timing_is_asc_order_map_s.
- by apply str_timing_is_asc_order_snapshot.
- by apply str_timing_is_asc_order_merge.
- by apply str_timing_is_asc_order_filter.
Qed.

Theorem occs_merge_never_right a f (s : stream a) : occs (merge s (never a) f) = occs s.
Proof.
rewrite /=.
rewrite occs_knit_nil_right.
move : (str_timing_is_asc_order_occs s).
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
    apply str_timing_is_asc_order_lt with (a0 := a1) (a' := a2) (s0 := (t2, a2) :: s2) => //.
    apply in_eq.
  rewrite IHs1 => //.
  by apply str_timing_is_asc_order_tail in H1.
Qed.

Theorem occs_merge_never_left a f (s : stream a) : occs (merge (never a) s f) = occs s.
Proof.
rewrite /=.
rewrite occs_knit_equation /=.
move : (str_timing_is_asc_order_occs s).
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
    apply str_timing_is_asc_order_lt with (a0 := a1) (a' := a2) (s0 := (t2, a2) :: s2) => //.
    apply in_eq.
  rewrite IHs1 => //.
  by apply str_timing_is_asc_order_tail in H1.
Qed.

Definition lift a b c (ca : cell a) (cb : cell b) (f : a -> b -> c) : cell c := apply (map_c f ca) cb.

Definition gate a (s : stream a) (c : cell bool) : stream a :=
  map_s fst (filter (fun ac => snd ac) (snapshot (fun a' cond => (a', cond)) s c)).

























