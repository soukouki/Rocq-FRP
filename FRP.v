(* 
FRPの表示的意味論をCoqに移植した。
元のソースコードはこのリンク先にある。 https://github.com/SodiumFRP/sodium/tree/master/denotational
 *)

Set Implicit Arguments.

Require Import ssreflect.
Require Import List Nat.
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
    case_eq (x1 ?= y1) => H2;
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
strはストリームの内部的な型を表す。
どの論理的時刻にどの値を持って発火するのかを表す。
元のコードではSとなっていたが、小文字にすると変数名とかぶりがちなのでstrとした。

cはセルの内部的な型を表す。
初期値と、それがどの論理的時刻にどの値で更新されるかを表す。
更新が発生しない論理的時刻のときは、何も表さない。
元のコードではCとなっていたが、小文字にすると変数名とかぶりがちなのでcelとした。

これらの型はlist型を使っているため、同じ論理的時刻に複数回発火したり、順番が異なるリストが生まれたりする。
ここでは、1つの論理的時刻には0または1回のイベントしか発火せず、リスト内の要素は論理的時刻が昇順となるように並んでいるものとする。
 *)
Definition str a := list (time * a).
Definition cel a := (a * (list (time * a)%type))%type.

(* 
#[bypass_check(positivity)]は、帰納型で矛盾を作る方法を阻止する為にあるエラーを無視する。
これを使った証明は健全では無いかもしれない。
しかし、streamとcellを元のHaskellのコードに似た形で作るには必須なため、ここでは受け入れることにする。
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

Axiom axiom_false : False.
Definition todo {a : Type} : a := False_rect _ axiom_false.

Require Import Recdef.

Function coalesce a (f : a -> a -> a) (s : str a) {measure length s} : str a :=
  match s with
  | (t1, a1) :: (t2, a2) :: tas => if t1 =? t2 then coalesce f ((t1, f a1 a2) :: tas) else (t1, a1) :: coalesce f ((t1,  a2) :: tas)
  | ta1 :: tas => todo
  | [] => []
  end.
Proof.
move => a f s ta1 tas t1 a1 H1 p tas0 t2 a2 H2 H3 H4 H5.
by [].

move => a f s ta1 tas t1 a1 H1 p tas0 t2 a2 H2 H3 H4 H5.
by [].
Qed.

Definition occs a (s : stream a): str a :=
  match s with
  | mk_stream s' => s'
  | never _ => []
  | map_s _ _ => []
  | snapshot _ _ _ => []
  | merge _ _ _ => []
  | filter _ _ => []
  | switch_s _ => []
  | execute _ => []
  | update _  => []
  | value _ _ => []
  | split _ => []
  end.

End FRP.

