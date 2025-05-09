Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
From CoqFRP Require Import FRP.
Import ListNotations.
Import Peano PeanoNat.Nat.

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
    | Lt => (ft1, f1 p0) :: steps_knit f1 p0 (fs1, ps)
    | Gt => (pt1, f0 p1) :: steps_knit f0 p1 (fs, ps1)
    | Eq => (ft1, f1 p1) :: steps_knit f1 p1 (fs1, ps1)
    end
  | ((ft1, f1) :: fs1, []) => (ft1, f1 p0) :: steps_knit f1 p0 (fs1, [])
  | ([], (pt1, p1) :: ps1) => (pt1, f0 p1) :: steps_knit f0 p1 ([], ps1)
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

(* 以下はoccs, stepsに関する定理 *)

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

Lemma coalesce_in_head a (f : a -> a -> a) (t1 : time) (a1 : a) (s1 : str a) :
  In t1 (map fst (coalesce f ((t1, a1) :: s1))).
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
    rewrite eqb_eq in H2.
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

Lemma steps_knit_nil_right p a (f0 : p -> a) (p0 : p) (cf : list (time * (p -> a))) :
  steps_knit f0 p0 (cf, []) = map (fun tp => (fst tp, (snd tp) p0)) cf.
Proof.
move : f0 p0.
induction cf as [ | [tf1 f1] cf1 ] => f0 p0.
  by rewrite steps_knit_equation.
rewrite steps_knit_equation.
by rewrite IHcf1.
Qed.

Lemma steps_knit_nil_left p a (f0 : p -> a) (p0 : p) (cp : list (time * p)) :
  steps_knit f0 p0 ([], cp) = map (fun tp => ((fst tp), f0 (snd tp))) cp.
Proof.
move : f0 p0.
induction cp as [ | [tp1 p1] cp1 ] => f0 p0.
  by rewrite steps_knit_equation.
rewrite steps_knit_equation.
by rewrite IHcp1.
Qed.

Lemma steps_knit_in_left p a (t : time) f1 a1 (cf1 : list (time * (p -> a))) (cp1 : list (time * p)) :
  In t (map fst cf1) ->
  In t (map fst (steps_knit f1 a1 (cf1, cp1))).
Proof.
Admitted.

Lemma steps_knit_in_right p a (t : time) f1 a1 (cf1 : list (time * (p -> a))) (cp1 : list (time * p)) :
  In t (map fst cp1) ->
  In t (map fst (steps_knit f1 a1 (cf1, cp1))).
Proof.
Admitted.






























