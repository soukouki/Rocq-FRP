(* 
FRPの表示的意味論をCoqに移植した。
元のソースコードはこのリンク先にある。 https://github.com/SodiumFRP/sodium/tree/master/denotational
 *)

Set Implicit Arguments.

Require Import ssreflect.
Require Import List Nat Recdef.
Import PeanoNat.Nat.
Import ListNotations.

Module FRP.

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

Infix "?=" := time_compare (at level 70).
Infix "=?" := time_eq (at level 70).
Infix "<?" := time_lt (at level 70).
Infix "<=?" := time_le (at level 70).
Infix ">?" := time_gt (at level 70).
Infix ">=?" := time_ge (at level 70).

End FRPNotations.

Import FRPNotations.

Lemma eqb_eq (x y : time) : x =? y = true <-> x = y.
Proof.
split.
- rewrite /time_eq.
  suff: time_compare x y = Eq -> x = y => [ H1 | ].
    case_eq (time_compare x y) => // H2 _.
    by apply H1.
  move: y.
  induction x as [ | x1 xs1] => y; [ by case y | ].
  case y => //= y1 ys1 H1.
  have: x1 = y1 => [ | H2 ].
    case_eq (x1 ?= y1)%nat => H2;
      rewrite H2 in H1 => //.
    by rewrite compare_eq_iff in H2.
  subst.
  apply /f_equal /IHxs1.
  by rewrite compare_refl in H1.
- move => <-.
  rewrite /time_eq.
  suff: time_compare x x = Eq.
    by move => ->.
  rewrite /time_compare.
  induction x => //.
  rewrite IHx.
  by rewrite compare_refl.
Qed.

(* 
strはストリームの発火する論理的時刻とその値をリストにしたものを持つ。
元のコードではSとなっていたが、小文字にすると変数名とかぶりがちなのでstrとした。

celはセルの初期値と、発火する論理的時刻とその値をリストにしたものを持つ。
元のコードではCとなっていたが、小文字にすると変数名とかぶりがちなのでcelとした。

これらの型はlist型を使っているため、同じ論理的時刻に複数回発火したり、順番が異なるようなリストについて考えないといけないことがある。
ここでは、1つの論理的時刻には0または1回のイベントしか発火せず、リスト内の要素は論理的時刻が昇順となるように並んでいるものと考えることにする。
 *)
Definition str a := list (time * a).
Definition cel a := (a * (list (time * a)%type))%type.

(* 
streamとcellはストリームとセルをそれぞれ表す。このstreamとcellは、プリミティブによって作られた、普通のストリームとセルである。

#[bypass_check(positivity)]は、帰納型で矛盾を作る方法を阻止する為にあるエラーを無視する。
このエラーはswitch_sとswitch_cの部分を除くと解決する。
これを使った証明は健全では無いかもしれないが、streamとcellを元のHaskellのコードに似た形で作るには必須なため、ここでは受け入れることにする。
 *)
#[bypass_check(positivity)] Inductive stream a :=
  | mk_stream : str a -> stream a
  | never : stream a
  | map_s prev : (prev -> a) -> stream prev -> stream a
  | snapshot prev_s prev_c : (prev_s -> prev_c -> a) -> stream prev_s -> cell prev_c -> stream a
  | merge : stream a -> stream a -> (a -> a -> a) -> stream a
  | filter : (a -> bool) -> stream a -> stream a
  | switch_s : cell (stream a) -> stream a
  | execute : stream (time -> a) -> stream a
  | update : cell a -> stream a
  | value : cell a -> time -> stream a
  | split : stream (list a) -> stream a
with cell a :=
  | constant : a -> cell a
  | hold : a -> stream a -> time -> cell a
  | map_c prev : (prev -> a) -> cell prev -> cell a
  | apply prev : cell (prev -> a) -> cell prev -> cell a
  | switch_c : cell (cell a) -> time -> cell a.

Definition at_ a (cel : cel a) (t : time) : a :=
  last (map snd (List.filter (fun ta => (fst ta) <? t) (snd cel))) (fst cel).

Definition chop_front a (cel : cel a) (t0 : time) :=
  (at_ cel t0, List.filter (fun ta => (fst ta) >=? t0) (snd cel)).

Function coalesce a (f : a -> a -> a) (s : str a) {measure length s} : str a :=
  match s with
  | (t1, a1) :: (t2, a2) :: tas =>
    if t1 =? t2
    then
      coalesce f ((t1, f a1 a2) :: tas)
    else
      (t1, a1) :: coalesce f ((t1,  a2) :: tas)
  | ta1 :: tas => ta1 :: coalesce f tas
  | [] => []
  end.
Proof.
- by move => a f s ta1 tas t1 a1 H1 H2 H3.
- by move => a f s ta1 tas t1 a1 H1 p tas0 t2 a2 H2 H3 H4 H5.
- by move => a f s ta1 tas t1 a1 H1 p tas0 t2 a2 H2 H3 H4 H5.
Qed.

Function occs_knit a (ab : (str a * str a)) {measure (fun (ab : str a * str a) => length (fst ab ++ snd ab)) ab} :=
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
- by move => a ab tas tbs p tas2 ta a0 H1 H2 p0 tbs2 tb b H3 H4 H5 H6.
- move => a ab tas tbs p tas2 ta a0 H1 H2 p0 tbs2 tb b H3 H4 H5 H6.
  rewrite /=.
  apply Lt.lt_n_S.
  rewrite 2!app_length.
  by apply Plus.plus_lt_compat_l.
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
- by move => p a f0 p0 fps fs ps H1 pt1p1 ps1 pt1 p1 H2 H3 H4.
- by move => p a f0 p0 fps fs ps H1 pt1p1 ps1 pt1 p1 H2 H3 H4.
- move => p a f0 p0 fps fs ps ft1f1 fs1 ft1 f1 H1 H2 pt1p1 ps1 pt1 p1 H3 H4 H5 H6.
  rewrite /= add_succ_r.
  by apply le_S.
- by move => p a f0 p0 fps fs ps ft1f1 fs1 ft1 f1 H1 H2 pt1p1 ps1 pt1 p1 H3 H4 H5 H6.
- move => p a f0 p0 fps fs ps ft1f1 fs1 ft1 f1 H1 H2 pt1p1 ps1 pt1 p1 H3 H4 H5 H6.
  by rewrite /= add_succ_r.
Qed.

Axiom axiom_False : False.
Definition TODO {a} := False_rect a axiom_False.

Fixpoint occs a (s_ : stream a): str a :=
  match s_ with
  | mk_stream s => s
  | never _ => []
  | map_s f s => map (fun ta => (fst ta, f (snd ta))) (occs s)
  | snapshot f s c => map (fun ta => (fst ta, f (snd ta) (at_ (steps c) (fst ta)))) (occs s)
  | merge sa sb f => coalesce f (occs_knit (occs sa, occs sb))
  | filter pred s => List.filter (fun ta => pred (snd ta)) (occs s)
  | switch_s _ => TODO
  | execute _ => TODO
  | update c  => snd (steps c)
  | value c t0 =>
    let
      cf := chop_front (steps c) t0
    in
      coalesce (fun x y => y) ((t0, fst cf) :: snd cf)
  | split s => TODO
  end
with steps a (c_ : cell a) : cel a :=
  match c_ with
  | constant a => (a, [])
  | hold a s t0 => (a, coalesce (fun x y => y) (List.filter (fun ta => fst ta >=? t0) (occs s)))
  | map_c f c =>
    let
      stp := steps c
    in
      (f (fst stp), map (fun ta => (fst ta, f (snd ta))) (snd stp))
  | apply cf cp =>
    let
      (f, fsts) := steps cf
    in let
      (p, psts) := steps cp
    in
      (f p, steps_knit f p (fsts, psts))
  | switch_c _ _ => TODO
  end.

Theorem occs_map_never a b (f : a -> b) : occs (map_s f (never a)) = occs (never b).
Proof.
done.
Qed.

Definition nth_sig a (l : list a) (n : nat | n < length l) : a.
Proof.
case n => n' H1.
case_eq (nth_error l n') => // H2.
by apply (iffRL (nth_error_Some l n')) in H1.
Qed.

Definition nth_sig_nth_error a (l : list a) n (H1 : n < length l) : Some (nth_sig l (exist (fun n0 : nat => n0 < length l) n H1)) = nth_error l n.
Proof.
case_eq (nth_error l n).
- move => x _.
  apply f_equal.
  move: (exist (fun n0 : nat => n0 < length l) n H1) => H2.
  
- move => H2.
  pose proof H1 as H1'.
  by rewrite -nth_error_Some in H1'.

Definition hog2 : {n : nat | n < length [1; 2; 3]}.
Proof.
by exists 2.
Qed.

Theorem hog3 : nth_sig [1; 2; 3] hog2 = 3.
Proof.
rewrite /nth_sig.

Definition str_timing_is_scratted a (s : str a) n m (H1 : n < length s) (H2 : m < length s) : Prop :=
  nth_sig

Theorem hoge : str_timing_is_scratted (occs (mk_stream [([1], 1); ([2], 2)])).
Proof.
rewrite /occs.
rewrite /str_timing_is_scratted.
move => n m H1 H2 H3.
case n.
- case m.
  rewrite /nth_error.
  


Theorem occs_merge_never_right a (f : a -> a -> a) (s : stream a) : occs (merge s (never a) f) = occs s.
Proof.
rewrite /=.
rewrite occs_knit_equation.
case (occs s).
  by rewrite coalesce_equation.
move => pt ps.
case pt => pt1 p1.
rewrite app_nil_r.
move: pt1 p1.
clear pt s.
induction ps.
  move => pt1 p1.
  by rewrite 2!coalesce_equation.
move => pt1 p1.
rewrite coalesce_equation.
case_eq a0.
move => pt2 p2 H1.
case_eq (pt1 =? pt2).
  move => H2.
  rewrite eqb_eq in H2.
  subst.
  rewrite IHps.
  


End FRP.

