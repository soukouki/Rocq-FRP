Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing Tactics.

(* 
// map, snapshot, merge, neverを含む例
public class Sample1 {
	public Sample1(Stream<Integer> sA1, Stream<Integer> sB1, Cell<Boolean> cFlag) {
		// hypothesis(different_timing(sA1, sB1))
		Stream<Integer> sA2 = sA1.map(n -> n + 1).snapshot(cFlag, (n, b) -> b ? n : 0);
		Stream<Integer> sB2 = sB1.merge(new Stream<Unit>.map(_ -> 1), (n, m) -> n, m);
		// check(different_timing(sA2, sB2))
		Stream<Integer> sC1 = sA2.merge(sB2, (a, b) -> a + b);
		// check(subset_timing(sA1, sC1))
		// check(subset_timing(sB1, sC1))
	}
}
 *)

Section Sample1_Sample1.

Variable a : Type.

Variable sA1 : stream a.
Variable sB1 : stream a.
Variable cFlag : cell a.

Hypothesis Hy1 : different_timing (stream_timing sA1) (stream_timing sB1).

Variable f1 : a -> a.
Variable f2 : a -> a -> a.
Definition sA2 := snapshot f2 (map_s f1 sA1) cFlag.

Variable f3 : a -> a -> a.
Definition sB2 := merge sB1 (never a) f3.

Variable f4 : a -> a -> a.
Definition sC1 := merge sA2 sB2 f4.

From Ltac2 Require Import Ltac2 Control Std Message.
Ltac2 clause_concl := {Std.on_hyps := None; Std.on_concl := Std.AllOccurrences}.
Ltac2 test_ (t : ident) :=
  Std.unfold([VarRef(t), AllOccurrences])(clause_concl).
Ltac2 test2 () :=
  print (Message.of_string "test1"); print (Message.of_string "test2").
Ltac2 Notation test := test_ ().

Proof Mode "Classic".

Theorem T1 : different_timing (stream_timing sA2) (stream_timing sB2).
Proof Mode "Ltac2".
test2().
Std.unfold([(reference:(sA2)), AllOccurrences])(clause_concl).
Std.unfold([(VarRef(ident:(sB2))), AllOccurrences])(clause_concl).
test_(ident:(sA2)).
Proof Mode "Classic".
rewrite /sA2 /sB2.
rewrite stream_timing_snapshot.
rewrite stream_timing_map_s.
rewrite stream_timing_merge_never_right.
apply Hy1.
Qed.

Theorem T2 : subset_timing (stream_timing sA1) (stream_timing sC1).
Proof Mode "Ltac2".
foo.
Proof Mode "Classic".

autounfold with frp.
rewrite /sC1.
rewrite /sA2 /sB2.
apply subset_timing_is_transitive with (b := stream_timing (snapshot f2 (map_s f1 sA1) cFlag)).
- rewrite stream_timing_snapshot.
  by rewrite stream_timing_map_s.
- by apply merge_subset_timing_left.
Qed.

Theorem T3 : subset_timing (stream_timing sB1) (stream_timing sC1).
rewrite /sC1.
rewrite /sA2 /sB2.
apply subset_timing_is_transitive with (b := stream_timing (merge sB1 (never a) f3)).
- by rewrite stream_timing_merge_never_right.
- by apply merge_subset_timing_right.
Qed.

End Sample1_Sample1.


