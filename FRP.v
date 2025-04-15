(* 
FRPの表示的意味論をCoqに移植した。
元のソースコードはこのリンク先にある。 https://github.com/SodiumFRP/sodium/tree/master/denotational
 *)

Set Implicit Arguments.

Require Import ssreflect.
Require Import List Nat Recdef.
Import PeanoNat.Nat.
Import ListNotations.

Require Import Top.Classical.
Import Classical.

Module FRP.

Create HintDb frp.

(* 
timeは1つの論理的時刻を表す。
timeが[1]のとき、それをSplitで分割すると[1, 0], [1, 1], ...というふうに分割される。
元のコードではTとなっていたが、小文字にすると変数名がかぶりがちなのでtimeとした。
 *)
Definition time := list nat.

(* 
time用の比較演算子を定義する。
 *)
Fixpoint time_compare (t1 t2 : time) : comparison :=
  match t1, t2 with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | h1 :: t1', h2 :: t2' =>
    match Nat.compare h1 h2 with
    | Eq => time_compare t1' t2'
    | c => c
    end
  end.

Definition time_eq (t1 t2 : time) : bool :=
  match time_compare t1 t2 with
  | Eq => true
  | _ => false
  end.
Definition time_lt (t1 t2 : time) : bool :=
  match time_compare t1 t2 with
  | Lt => true
  | _ => false
  end.
Definition time_le (t1 t2 : time) : bool :=
  match time_compare t1 t2 with
  | Lt | Eq => true
  | Gt => false
  end.
Definition time_gt (t1 t2 : time) : bool :=
  match time_compare t1 t2 with
  | Gt => true
  | _ => false
  end.
Definition time_ge (t1 t2 : time) : bool :=
  match time_compare t1 t2 with
  | Gt | Eq => true
  | Lt => false
  end.

Module FRPNotations.

Declare Scope frp_scope.

Infix "?=" := time_compare (at level 70) : frp_scope.
Infix "=?" := time_eq (at level 70) : frp_scope.
Infix "<?" := time_lt (at level 70) : frp_scope.
Infix "<=?" := time_le (at level 70) : frp_scope.
Infix ">?" := time_gt (at level 70) : frp_scope.
Infix ">=?" := time_ge (at level 70) : frp_scope.

End FRPNotations.

Import FRPNotations.
Open Scope frp_scope.

Lemma time_eq_eq (x y : time) : x =? y = true <-> x = y.
Proof.
split.
- rewrite /time_eq.
  suff: time_compare x y = Eq -> x = y => [ H1 | ].
    case_eq (time_compare x y) => // H2 _.
    by apply H1.
  move: y.
  induction x as [ | x1 xs1 ] => y; [ by case y | ].
  case y => //= y1 ys1 H1.
  have: x1 = y1 => [ | H2 ].
    case_eq (x1 ?= y1)%nat => H2;
      rewrite H2 in H1 => //.
    by rewrite compare_eq_iff in H2.
  subst.
  apply /f_equal /IHxs1.
  by rewrite compare_refl in H1.
- move=> <-.
  rewrite /time_eq.
  suff: time_compare x x = Eq.
    by move=> ->.
  rewrite /time_compare.
  induction x => //.
  rewrite IHx.
  by rewrite compare_refl.
Qed.

Lemma time_compare_lt (x y : time) : x ?= y = Lt <-> x <? y = true.
Proof.
split.
- move=> H1.
  rewrite /time_lt.
  by rewrite H1.
- rewrite /time_lt.
  by case (x ?= y).
Qed.

Lemma time_compare_eq (x y : time) : x ?= y = Eq <-> x =? y = true.
Proof.
split.
- move=> H1.
  rewrite /time_eq.
  by rewrite H1.
- rewrite /time_eq.
  by case (x ?= y).
Qed.

Lemma time_compare_gt (x y : time) : x ?= y = Gt <-> x >? y = true.
Proof.
split.
- move=> H1.
  rewrite /time_gt.
  by rewrite H1.
- rewrite /time_gt.
  by case (x ?= y).
Qed.

Lemma time_eq_true (x : time) : x =? x = true.
Proof.
by rewrite time_eq_eq.
Qed.

Lemma time_lt_false (x : time) : (x <? x) = false.
Proof.
rewrite /time_lt.
suff: x ?= x = Eq => [ -> // | ].
induction x => //.
by rewrite /= compare_refl.
Qed.

Lemma time_gt_false (x : time) : (x >? x) = false.
Proof.
rewrite /time_gt.
suff: x ?= x = Eq => [ -> // | ].
induction x => //.
by rewrite /= compare_refl.
Qed.

Lemma time_le_true (x : time) : (x <=? x) = true.
Proof.
rewrite /time_le.
suff: x ?= x = Eq => [ -> // | ].
by rewrite time_compare_eq time_eq_true.
Qed.

Lemma time_ge_true (x : time) : (x >=? x) = true.
Proof.
rewrite /time_ge.
suff: x ?= x = Eq => [ -> // | ].
by rewrite time_compare_eq time_eq_true.
Qed.

Lemma time_gt_not_le (x y : time) : (x >? y) = true <-> (x <=? y) = false.
Proof.
split.
- rewrite -time_compare_gt => H1.
  rewrite /time_le.
  by rewrite H1.
- rewrite /time_le.
  rewrite -time_compare_gt.
  by case (x ?= y).
Qed.

Lemma time_lt_not_ge (x y : time) : (x <? y) = true <-> (x >=? y) = false.
Proof.
split.
- rewrite -time_compare_lt => H1.
  rewrite /time_ge.
  by rewrite H1.
- rewrite /time_ge.
  rewrite -time_compare_lt.
  by case (x ?= y).
Qed.

Lemma time_lt_le_eq (x y : time) : x <? y = false /\ x <=? y = true <-> x = y.
Proof.
split.
- case => H1 H2.
  case_eq (x ?= y).
  + by rewrite time_compare_eq time_eq_eq.
  + by rewrite time_compare_lt H1.
  + rewrite time_compare_gt.
    by rewrite time_gt_not_le H2.
- move=> <-.
  split.
  + by rewrite time_lt_false.
  + by rewrite time_le_true.
Qed.

Lemma time_gt_ge_eq (x y : time) : x >? y = false /\ x >=? y = true <-> x = y.
Proof.
split.
- case=> H1 H2.
  case_eq (x ?= y).
  + by rewrite time_compare_eq time_eq_eq.
  + rewrite time_compare_lt.
    by rewrite time_lt_not_ge H2.
  + by rewrite time_compare_gt H1.
- move=> <-.
  split.
  + by rewrite time_gt_false.
  + by rewrite time_ge_true.
Qed.

Lemma time_lt_not_eq (x y : time) : x <? y = true -> x =? y = false.
Proof.
move => H1.
rewrite /time_eq.
rewrite -time_compare_lt in H1.
by rewrite H1.
Qed.

Lemma time_gt_not_eq (x y : time) : x >? y = true -> x =? y = false.
Proof.
move => H1.
rewrite /time_eq.
rewrite -time_compare_gt in H1.
by rewrite H1.
Qed.

Lemma time_eq_sym (x y : time) : (x =? y) = (y =? x).
Proof.
have: forall a b, a =? b = true -> b =? a = true => [ a b H1 | H1 ].
  rewrite time_eq_eq.
  by rewrite time_eq_eq in H1.
case_eq (x =? y) => H2; symmetry.
- by apply H1.
- Search time_eq false.
  Search false not.
  rewrite -Bool.not_true_iff_false => H3.
  rewrite -Bool.not_true_iff_false in H2.
  apply H2.
  by apply H1.
Qed.

Lemma time_lt_gt (x y : time) : (x <? y) = (y >? x).
Proof.
case_eq (x ?= y) => H1.
- rewrite /time_lt.
  rewrite H1.
  rewrite /time_gt.
  rewrite time_compare_eq in H1.
  rewrite time_eq_sym in H1.
  rewrite -time_compare_eq in H1.
  by rewrite H1.
- rewrite /time_lt.
  rewrite H1; symmetry.
  move: y H1.
  induction x as [ | x1 xs1 ] => [ [ ] // | ].
  case=> // y1 ys1 H1.
  rewrite /time_gt.
  suff: y1 :: ys1 ?= x1 :: xs1 = Gt.
    by move=> ->.
  rewrite /=.
  case_eq (y1 ?= x1)%nat => // H2.
  + suff: ys1 >? xs1 = true.
      rewrite /time_gt.
      by case (ys1 ?= xs1).
    apply IHxs1.
    rewrite compare_eq_iff eq_sym_iff -compare_eq_iff in H2.
    by rewrite /= H2 in H1.
  + rewrite /= in H1.
    rewrite compare_lt_iff in H2.
    have: x1 > y1 => // H2'.
    rewrite Compare_dec.nat_compare_gt in H2'.
    by rewrite H2' in H1.
- rewrite time_compare_gt in H1.
  have: x <? y = false => [ | H2 ].
    
  have: y >? x = false => [ | H3 ].
    admit.
  by rewrite H2 H3.



- rewrite /time_lt.
  rewrite H1; symmetry.
  move: y H1.
  induction x as [ | x1 xs1 ] => [ [ ] // | ].
  case=> // y1 ys1 H1.
  case_eq (y1 :: ys1 ?= x1 :: xs1).
  + rewrite time_compare_eq time_eq_eq => ->.
    by rewrite time_gt_false.
  + move => H2.
    rewrite /time_gt.
    by rewrite H2.
  + move => H2.
    exfalso.
    case_eq (y1 ?= x1)%nat.
    * move => H3.
      rewrite /time_compare in H2.
      rewrite H3 in H2.
      Search time_compare time_gt

Qed.

(* 
strはストリームの発火する論理的時刻とその値をリストにしたものを持つ。
元のコードではSとなっていたが、  小文字にすると変数名とかぶりがちなのでstrとした。

celはセルの初期値と、発火する論理的時刻とその値をリストにしたものを持つ。
元のコードではCとなっていたが、小文字にすると変数名とかぶりがちなのでcelとした。

これらの型はlist型を使っているため、同じ論理的時刻に複数回発火したり、順番が異なるようなリストについて考えないといけないことがある。
ここでは、1つの論理的時刻には0または1回のイベントしか発火せず、リスト内の要素は論理的時刻が昇順となるように並んでいるものと考えることにする。
 *)
Definition str a := list (time * a).
Definition cel a := (a * (list (time * a)%type))%type.

Fixpoint str_timing_is_asc_order a (s : str a) : bool :=
  match s with
  | nil => true
  | (t1, a1) :: nil => true
  | (t1, a1) :: ((t2, a2) :: _) as tas => (t1 <? t2) && str_timing_is_asc_order tas
  end.

Lemma str_timing_is_asc_order_duplication a t (a1 a2 : a) as1 :
  str_timing_is_asc_order ((t, a1) :: (t, a2) :: as1) = false.
Proof.
rewrite /=.
rewrite Bool.andb_false_iff.
left.
by apply time_lt_false.
Qed.

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

Lemma str_timing_is_asc_order_first_gt a (ta1 ta2 : time * a) tas2 :
  str_timing_is_asc_order (ta1 :: ta2 :: tas2) = true -> fst ta1 <? fst ta2 = true.
Proof.
case ta1 => t1 a1.
case ta2 => t2 a2.
rewrite /= => H1.
rewrite Bool.andb_true_iff in H1.
by case H1.
Qed.

(* 
streamとcellはストリームとセルをそれぞれ表す。このstreamとcellは、プリミティブによって作られた、普通のストリームとセルである。

#[bypass_check(positivity)]は、帰納型で矛盾を作る方法を阻止する為にあるエラーを無視する。
このエラーはswitch_sとswitch_cの部分を除くと解決する。
これを使った証明は健全では無いかもしれないが、streamとcellを元のHaskellのコードに似た形で作るには必須なため、ここでは受け入れることにする。
 *)
Inductive stream a :=
  | mk_stream : { s : str a | str_timing_is_asc_order s = true } -> stream a
  | never : stream a
  | map_s prev : (prev -> a) -> stream prev -> stream a
  | snapshot prev_s prev_c : (prev_s -> prev_c -> a) -> stream prev_s -> cell prev_c -> stream a
  | merge : stream a -> stream a -> (a -> a -> a) -> stream a
  | filter : (a -> bool) -> stream a -> stream a
  (* | switch_s : cell (stream a) -> stream a *)
  | execute : stream (time -> a) -> stream a
  | update : cell a -> stream a
  | value : cell a -> time -> stream a
  | split : stream (list a) -> stream a
with cell a :=
  | constant : a -> cell a
  | hold : a -> stream a -> time -> cell a
  | map_c prev : (prev -> a) -> cell prev -> cell a
  | apply prev : cell (prev -> a) -> cell prev -> cell a
  (* | switch_c : cell (cell a) -> time -> cell a *).

Definition at_ a (cel : cel a) (t : time) : a :=
  last (map snd (List.filter (fun ta => (fst ta) <? t) (snd cel))) (fst cel).

Definition chop_front a (cel : cel a) (t0 : time) :=
  (at_ cel t0, List.filter (fun ta => (fst ta) >=? t0) (snd cel)).

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

Lemma str_timing_is_asc_order_coalesce a f (s : str a) :
  str_timing_is_asc_order s = true -> coalesce f s = s.
Proof.
move => H1.
induction s as [ | ta1 ].
  by rewrite coalesce_equation.
move: H1.
case ta1 => t1 a1 H1; clear ta1.
move: IHs H1.
case s.
- move => _ _.
  by rewrite 2!coalesce_equation.
- move => ta2 tas2.
  case ta2 => t2 a2 H1 H2; clear ta2.
  rewrite coalesce_equation.
  case_eq (t1 =? t2) => H3.
  + exfalso.
    apply str_timing_is_asc_order_first_gt in H2.
    rewrite /= in H2.
    rewrite time_eq_eq in H3.
    subst.
    by rewrite time_lt_false in H2.
  + rewrite H1 => //.
    by apply str_timing_is_asc_order_tail in H2.
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

Lemma occs_knit_nil_right a (s : str a) :
  occs_knit (s, []) = s.
Proof.
rewrite occs_knit_equation.
case s => // ta1 tas1.
rewrite app_nil_r.
by case ta1.
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

Definition maybe a b (vb : b) (f : a -> b) (opt : option a) : b :=
  match opt with
  | None => vb
  | Some va => f va
  end.

Definition concat_map a b (f : a -> list b) (l : list a) : list b :=
  concat (map f l).

Fixpoint number_with_i a b (f : a -> nat -> b) (l : list a) (n : nat) : list b :=
  match l with
  | nil => []
  | a1 :: l1 => f a1 n :: number_with_i f l1 (S n)
  end.

Definition number_with a b (f : a -> nat -> b) (l : list a) : list b :=
  number_with_i f l 0.

Fixpoint occs a (s_ : stream a) : str a :=
  match s_ with
  | mk_stream s => proj1_sig s
  | never _ => []
  | map_s f s => map (fun ta => (fst ta, f (snd ta))) (occs s)
  | snapshot f s c => map (fun ta => (fst ta, f (snd ta) (at_ (steps c) (fst ta)))) (occs s)
  | merge sa sb f => coalesce f (occs_knit (occs sa, occs sb))
  | filter pred s => List.filter (fun ta => pred (snd ta)) (occs s)
  | execute s => map (fun tma => (fst tma, (snd tma) (fst tma))) (occs s)
  | update c  => snd (steps c)
  | value c t0 =>
    let cf := chop_front (steps c) t0 in
    coalesce (fun x y => y) ((t0, fst cf) :: snd cf)
  | split s =>
    let spl := fun tas : (time * list a) =>
      let (t1, as1) := tas in
      number_with (fun a n => (t1 ++ [n], a)) as1 in
    concat (map spl (coalesce (fun x y => x ++ y) (occs s)))
  end
with steps a (c_ : cell a) : cel a :=
  match c_ with
  | constant a => (a, [])
  | hold a s t0 => (a, coalesce (fun x y => y) (List.filter (fun ta => fst ta >=? t0) (occs s)))
  | map_c f c =>
    let stp := steps c in
    (f (fst stp), map (fun ta => (fst ta, f (snd ta))) (snd stp))
  | apply cf cp =>
    let (f, fsts) := steps cf in
    let (p, psts) := steps cp in
    (f p, steps_knit f p (fsts, psts))
  end.

Theorem occs_map_never a b (f : a -> b) : occs (map_s f (never a)) = occs (never b).
Proof.
done.
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

Lemma coalesce_le a (f : a -> a -> a) t1 a1 t2 a2 tas :
  t1 <? t2 = true ->
  coalesce f ((t1, a1) :: (t2, a2) :: tas) = (t1, a1) :: coalesce f ((t2, a2) :: tas).
Proof.
move => H1.
rewrite {1}coalesce_equation.
apply time_lt_not_eq in H1.
by rewrite H1.
Qed.

Lemma str_timing_is_asc_order_merge a (s1 s2 : stream a) (f : a -> a -> a) :
  str_timing_is_asc_order (occs s1) = true ->
  str_timing_is_asc_order (occs s2) = true ->
  str_timing_is_asc_order (occs (merge s1 s2 f)) = true.
Proof.
rewrite /=.
move : (occs s1) => tas0a H1.
move : (occs s2) => tas0b H2.
induction tas0a as [ | ta1a tas1a IHa ].
- induction tas0b as [ | ta1b tas1b IHb ].
  + by rewrite occs_knit_equation coalesce_equation.
  + rewrite occs_knit_equation /=.
    by rewrite str_timing_is_asc_order_coalesce.
- induction tas0b as [ | ta1b tas1b IHb ].
  + rewrite occs_knit_equation /=.
    move: ta1a H1.
    case => t1a a1a H1.
    rewrite app_nil_r.
    by rewrite str_timing_is_asc_order_coalesce.
  + move : ta1a ta1b H1 H2 IHa IHb.
    case => t1a a1a.
    case => t1b a1b H1 H2 IHa IHb.
    rewrite occs_knit_equation.
    case_eq (t1a <=? t1b) => H3.
    * move : tas1a tas1b H1 H2 IHa IHb.
      case => // [ | ta2a a2a ].
      -- move => tas1b _ H2 IHa IHb.
         rewrite occs_knit_equation /=.
         have : str_timing_is_asc_order ((t1a, a1a) :: (t1b, a1b) :: tas1b) = true => [ | H4 ].
           rewrite /=.
           rewrite Bool.andb_true_iff.
           split.
           ++ case_eq (t1a <? t1b) => // H4.
              exfalso.
              have : t1a = t1b => [ | H5 ].
                by rewrite -time_lt_le_eq.
              subst; clear H3 H4.
Restart.
rewrite /=.
move : (occs s1) => tas0 H1.
move : (occs s2) => tbs0 H2.
suff : str_timing_is_asc_order (occs_knit (tas0, tbs0)) = true => [ H3 | ].
  by rewrite str_timing_is_asc_order_coalesce.
induction tas0 as [ | [ ta1 a1 ] tas1 IHa ].
  by rewrite occs_knit_equation /=.
induction tbs0 as [ | [ tb1 b1 ] tbs1 IHb ].
  by rewrite occs_knit_nil_right.
rewrite occs_knit_equation.
case_eq (ta1 <=? tb1) => H3.
- rewrite /str_timing_is_asc_order.
  rewrite {2}/str_timing_is_asc_order in IHa.
  rewrite IHa; clear IHa.
  + by apply str_timing_is_asc_order_tail in H1.
  + case tas1.
    * rewrite occs_knit_equation /=.
      rewrite Bool.andb_true_iff.
      split => //.
Restart.
rewrite /=.
move : (occs s1) => tas0 H1.
move : (occs s2) => tbs0 H2.
suff : str_timing_is_asc_order (occs_knit (tas0, tbs0)) = true => [ H3 | ].
  by rewrite str_timing_is_asc_order_coalesce.
clear s1 s2 f.
induction tas0 as [ | [ ta1 a1 ] tas1 IHa ].
  by rewrite occs_knit_equation /=.
induction tbs0 as [ | [ tb1 b1 ] tbs1 IHb ].
  by rewrite occs_knit_nil_right.
rewrite occs_knit_equation.
case_eq (ta1 <=? tb1) => H3.
- (* ta1 = tb1の場合にはそもそもasc_orderでは無いので、そもそもこの命題は証明できない *)
Restart.
rewrite /=.
move : (occs s1) => tas0 H1.
move : (occs s2) => tbs0 H2.
clear s1 s2.
induction tas0 as [ | ta1 tas1 IHa ].
- induction tbs0 as [ | tb1 tbs1 IHb ].
  + by rewrite occs_knit_equation coalesce_equation.
  + rewrite occs_knit_equation /=.
    by rewrite str_timing_is_asc_order_coalesce.
- induction tbs0 as [ | tb1 tbs1 IHb ].
  + rewrite occs_knit_equation /=.
    move: ta1 H1.
    case => t1a a1a H1.
    rewrite app_nil_r.
    by rewrite str_timing_is_asc_order_coalesce.
  + have : str_timing_is_asc_order tas1 = true.
      by apply str_timing_is_asc_order_tail in H1.
    move => H1'.
    specialize (IHa H1').
    have : str_timing_is_asc_order tbs1 = true.
      by apply str_timing_is_asc_order_tail in H2.
    move => H2'.
    specialize (IHb H2').
    clear H1' H2'.
    move : ta1 tb1 H1 H2 IHa IHb.
    move => [ta1 a1] [tb1 b1] H1 H2 IHa IHb.
    rewrite occs_knit_equation.
    case_eq (ta1 ?= tb1).
    * rewrite time_compare_eq time_eq_eq => Heq.
      apply Logic.eq_sym in Heq; subst.
      rewrite time_le_true.
      move : IHa.
      remember (occs_knit (tas1, (ta1, b1) :: tbs1)) as s.
      rewrite -Heqs.
      case_eq s.
      -- move => _ _.
         by rewrite 2!coalesce_equation.
      -- case => ts1 s1 ss1 Hs H3.
         rewrite coalesce_equation.
         have : ta1 =? ts1 = true.
Restart.
rewrite /=.
move : (occs s1) => tas0 H1.
move : (occs s2) => tbs0 H2.
clear s1 s2.
induction tas0 as [ | ta1 tas1 IHa ].
- induction tbs0 as [ | tb1 tbs1 IHb ].
  + by rewrite occs_knit_equation coalesce_equation.
  + rewrite occs_knit_equation /=.
    by rewrite str_timing_is_asc_order_coalesce.
- induction tbs0 as [ | tb1 tbs1 IHb ].
  + rewrite occs_knit_equation /=.
    move: ta1 H1.
    case => t1a a1a H1.
    rewrite app_nil_r.
    by rewrite str_timing_is_asc_order_coalesce.
  + have : str_timing_is_asc_order tas1 = true.
      by apply str_timing_is_asc_order_tail in H1.
    move => H1'.
    specialize (IHa H1').
    have : str_timing_is_asc_order tbs1 = true.
      by apply str_timing_is_asc_order_tail in H2.
    move => H2'.
    specialize (IHb H2').
    clear H1' H2'.
    move : ta1 tb1 H1 H2 IHa IHb.
    case => at1 a1.
    case => bt1 b1.
    move => H1 H2 IHa IHb.
    rewrite occs_knit_equation.
    case_eq (at1 ?= bt1) => H3.
    * rewrite time_compare_eq time_eq_eq in H3.
      subst.
      rewrite time_le_true.
      clear IHb.
      have : occs_knit (tas1, (bt1, b1) :: tbs1) = (bt1, b1) :: occs_knit (tas1, tbs1).
        clear IHa; move : tas1 H1 H2.
        case => [ H1 H2 | [at2 a2] tas2 H1 H2 ].
          by rewrite 2!occs_knit_equation.
        rewrite occs_knit_equation.
        have : at2 <=? bt1 = false.
          apply str_timing_is_asc_order_first_gt in H1; rewrite /fst in H1.
          rewrite -time_gt_not_le.
          Search time_lt time_gt.


Admitted.

Lemma str_timing_is_asc_order_filter a (f : a -> bool) (s : stream a) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (filter f s)) = true.
Proof.


Admitted.

Lemma str_timing_is_asc_order_execute a (s : stream (time -> a)) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (execute s)) = true.
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

Lemma str_timing_is_asc_order_update a (c : cell a) :
  str_timing_is_asc_order (occs (update c)) = true.
Proof.
Admitted.

Lemma str_timing_is_asc_order_value a (c : cell a) (t0 : time) :
  str_timing_is_asc_order (occs (value c t0)) = true.
Proof.
Admitted.

Lemma str_timing_is_asc_order_split a (s : stream (list a)) :
  str_timing_is_asc_order (occs s) = true -> str_timing_is_asc_order (occs (split s)) = true.
Proof.
rewrite /=.
move : (occs s) => tas0 H1.
induction tas0 as [ | ta1 tas1 IH ].
  by rewrite coalesce_equation.
Search coalesce.
rewrite str_timing_is_asc_order_coalesce => //.
rewrite str_timing_is_asc_order_coalesce in IH.
  by apply str_timing_is_asc_order_tail in H1.
rewrite /=.
rewrite /str_timing_is_asc_order.
rewrite IH.

Admitted.

Theorem str_timing_is_asc_order_occs a (s : stream a) :
  str_timing_is_asc_order (occs s) = true.
Proof.
induction s.
- rewrite /=.
  by apply (proj2_sig s).
- trivial.
- by apply str_timing_is_asc_order_map_s.
- by apply str_timing_is_asc_order_snapshot.
- by apply str_timing_is_asc_order_merge.
- by apply str_timing_is_asc_order_filter.
- by apply str_timing_is_asc_order_execute.
- by apply str_timing_is_asc_order_update.
- by apply str_timing_is_asc_order_value.
- by apply str_timing_is_asc_order_split.
Qed.

Lemma coalesce_eq a f (ps : str a) :
  str_timing_is_asc_order ps = true -> coalesce f ps = ps.
Proof.
induction ps.
  by rewrite coalesce_equation.
move => H1.
rewrite coalesce_equation.
move: H1.
case_eq a0.
move => pt1 p1 H2 H1.
case_eq ps.
  move => H3.
  subst.
  by rewrite IHps.
move => pa ps2 H4.
case_eq pa => pt2 p2 H5.
subst.
case_eq (pt1 =? pt2).
- move => H4.
  rewrite time_eq_eq in H4.
  subst.
  by rewrite str_timing_is_asc_order_duplication in H1.
- move => H4.
  rewrite IHps => //.
  by apply str_timing_is_asc_order_tail in H1.
Qed.

Theorem occs_merge_never_right a (f : a -> a -> a) (s : stream a) :
  str_timing_is_asc_order (occs s) = true ->
  occs (merge s (never a) f) = occs s.
Proof.
rewrite /=.
move: (occs s) => occs_s H1.
rewrite occs_knit_equation.
case_eq (occs_s).
  by rewrite coalesce_equation.
move => pt ps H2.
subst.
move: H1.
case pt => pt1 p1 H1.
rewrite app_nil_r.
by apply coalesce_eq.
Qed.
Hint Rewrite occs_merge_never_right : frp.

Theorem occs_merge_never_left a (f : a -> a -> a) (s : stream a) :
  str_timing_is_asc_order (occs s) = true ->
  occs (merge (never a) s f) = occs s.
Proof.
rewrite /=.
move: (occs s) => occs_s H1.
rewrite occs_knit_equation /=.
by apply coalesce_eq.
Qed.
Hint Rewrite occs_merge_never_left : frp.

Definition is_some a (x : option a) :=
  match x with
  | None => false
  | Some _ => true
  end.

Definition has_same_time (ta tb : list time) : bool :=
  let find_tb := fun a => is_some (find (time_eq a) tb) in
  is_some (find find_tb ta).

Definition is_stream_fireing_at_a_time a b (sa : stream a) (sb : stream b) :=
  let oa := map fst (occs sa) in
  let ob := map fst (occs sb) in
  has_same_time oa ob.

Lemma occs_map_s_mk_stream a b (s : { s : str a | str_timing_is_asc_order s = true }) (f : a -> b) :
  occs (map_s f (mk_stream s)) = map (fun ta => (fst ta, f (snd ta))) (proj1_sig s).
Proof.
done.
Qed.
Hint Rewrite occs_map_s_mk_stream : frp.

Definition test_frp_sPlusDelta (sPlus : stream unit) :=
  map_s (fun _ => 1) sPlus.
Variable test_frp_cValue1 : cell nat.
Definition test_frp_sUpdate (sPlus : stream unit) :=
  snapshot (fun i x => i + x) (test_frp_sPlusDelta sPlus) test_frp_cValue1.
Definition test_frp_cValue2 (t0 : time) (sPlus : stream unit) :=
  hold 0 (test_frp_sUpdate sPlus) t0.
Axiom test_frp_cValue1_eq_test_frp_cValue2 :
  forall t0 sPlus, test_frp_cValue1 = test_frp_cValue2 t0 sPlus.
Definition test_frp_return (t0 : time) (sPlus : stream unit) :=
  test_frp_cValue1.

Theorem test_frp_sPlusDelta_and_test_frp_sUpdate_is_fireing_at_a_time :
  forall sPlus, is_stream_fireing_at_a_time (test_frp_sPlusDelta sPlus) (test_frp_sUpdate sPlus) = true.
Proof.
have : { s : str unit | str_timing_is_asc_order s = true }.
  exists [([1], tt)].
  by [].
move => s.
exists (mk_stream s).
rewrite /is_stream_fireing_at_a_time.
by autorewrite with frp.
Qed.

Variable test_frp_sStreamLoop : stream unit.
Definition test_frp_sUpdate (sPlus : stream unit) :=
  merge test_frp_sStreamLoop sPlus (fun x y => x).
Axiom test_frp_sStreamLoop_eq_test_frp_sUpdate :
  forall sPlus, test_frp_sStreamLoop = test_frp_sUpdate sPlus.
Definition test_frp_return (t0 : time) (sPlus : stream unit) :=
  hold 0 (map_s (fun u => 1) test_frp_sStreamLoop) t0.

Theorem test_frp_streamLoop_correct : False.
Proof.
suff: exists sPlus, occs test_frp_sStreamLoop <> occs (test_frp_sUpdate sPlus).
  move => H1.
  rewrite exists_iff_not_forall_not in H1.
  apply H1 => sStreamLoop.
  apply.
  by rewrite -test_frp_sStreamLoop_eq_test_frp_sUpdate.
exists (mk_stream [([1], tt)]).
rewrite /=.
rewrite occs_knit_equation.





End FRP.

