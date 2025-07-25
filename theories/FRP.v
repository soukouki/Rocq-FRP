Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List Recdef Nat.
Import ListNotations.
Import Peano PeanoNat.Nat.

(* splitプリミティブを実装しないため、論理的時刻はnatで十分 *)
Definition time := nat.

Definition str a := list (time * a).
Definition cel a := (a * (list (time * a)))%type.

Fixpoint is_asc_timing a (s : str a) : bool :=
  match s with
  | nil => true
  | (t1, a1) :: nil => true
  | (t1, a1) :: ((t2, a2) :: _) as tas => (t1 <? t2) && is_asc_timing tas
  end.

(* 本来は更にプリミティブが何種類かあるが、今回証明するモデルでは省略する *)
Inductive stream a :=
  | mk_stream : { s : str a | is_asc_timing s = true } -> stream a
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

Definition lift a b c (ca : cell a) (cb : cell b) (f : a -> b -> c) : cell c := apply (map_c f ca) cb.

Definition gate a (s : stream a) (c : cell bool) : stream a :=
  map_s fst (filter (fun ac => snd ac) (snapshot (fun a' cond => (a', cond)) s c)).



























