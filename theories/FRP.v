
Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
Import ListNotations.
Import PeanoNat.Nat.

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

Inductive stream a :=
  | mk_stream : { s : str a | str_timing_is_asc_order s = true } -> stream a
  | never : stream a
  | map_s prev : (prev -> a) -> stream prev -> stream a
  | snapshot prev_s prev_c : (prev_s -> prev_c -> a) -> stream prev_s -> cell prev_c -> stream a
  | merge : stream a -> stream a -> (a -> a -> a) -> stream a
  | filter : (a -> bool) -> stream a -> stream a
with cell a :=
  | constant : a -> cell a
  | hold : a -> stream a -> time -> cell a
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
  | hold a s t0 => (a, coalesce (fun x y => y) (List.filter (fun ta => t0 <? fst ta) (occs s)))
  | map_c f c =>
    let stp := steps c in
    (f (fst stp), map (fun ta => (fst ta, f (snd ta))) (snd stp))
  | apply cf cp =>
    let (f, fsts) := steps cf in
    let (p, psts) := steps cp in
    (f p, steps_knit f p (fsts, psts))
  end.

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

(* 2時間位格闘したけれど示せなかった *)
Lemma str_timing_is_asc_order_gt a t0 a0 (s0 : str a) :
  str_timing_is_asc_order ((t0, a0) :: s0) = true ->
  forall t' a', In (t', a') s0 -> t0 < t'.
Proof.
Admitted.

Lemma str_timing_is_asc_order_first_gt a (ta1 ta2 : time * a) tas2 :
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
  + by apply str_timing_is_asc_order_gt with (a0 := a0).
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
  by apply str_timing_is_asc_order_first_gt in H1.
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
  by apply str_timing_is_asc_order_first_gt in H1.
Qed.

Lemma str_timing_is_asc_order_coalesce_ignore_head_value a (s0 : str a) (f : a -> a -> a) t0 a0 b0 :
  str_timing_is_asc_order (coalesce f ((t0, a0) :: s0)) = true ->
  str_timing_is_asc_order (coalesce f ((t0, b0) :: s0)) = true.
Proof.
move : t0 a0 b0.
induction s0 as [ | [t1 a1] s1] => [ t0 a0 b0 | t0 a0 b0 ].
  by rewrite 4!coalesce_equation.
rewrite coalesce_equation [coalesce f ((t0, b0) :: _ )]coalesce_equation.
case_eq (t0 =? t1) => H1.
- rewrite eqb_eq in H1.
  by apply IHs1.
- rewrite eqb_neq in H1. (* いらんかも *)
  Search str_timing_is_asc_order.
  move => H2.
  apply str_timing_is_asc_order_tail in H2.
  apply str_timing_is_asc_order_head => // t' H3.
  
Admitted.

Lemma str_timing_is_asc_order_coalesce a (s : str a) (f : a -> a -> a) :
  str_timing_is_asc_order s = true -> str_timing_is_asc_order (coalesce f s) = true.
Proof.
induction s as [ | ta0 ] => [ _ | ].
  by rewrite coalesce_equation.
rewrite coalesce_equation.
case ta0 => t0 a0.
move : IHs.
case s => [ IH _ | ta1 s1 ].
  by rewrite coalesce_equation.
case ta1 => t1 a1 => IH H1.
case_eq (t0 =? t1) => H2.
- apply str_timing_is_asc_order_tail in H1.
  apply IH in H1.
  rewrite eqb_eq in H2.
  subst.
  clear ta0 s ta1 IH.
  move : H1.

Admitted.

Lemma str_timing_is_asc_order_merge a (s1 s2 : stream a) (f : a -> a -> a) :
  str_timing_is_asc_order (occs s1) = true ->
  str_timing_is_asc_order (occs s2) = true ->
  str_timing_is_asc_order (occs (merge s1 s2 f)) = true.
Proof.
rewrite /=.
move : (occs s1) (occs s2) => tas1 tas2.
induction tas1 as [ | ] => [ _ H1 | H2 H3 ].
- rewrite occs_knit_equation /=.
  by apply str_timing_is_asc_order_coalesce.
- rewrite occs_knit_equation.

Admitted.

Lemma str_timing_is_asc_order_filter a (f : a -> bool) (s : stream a) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (filter f s)) = true.
Proof.
Admitted.

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
























