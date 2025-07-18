Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing Tactics.

Set Default Proof Mode "Ltac2".

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

Proposition T1 : different_timing (stream_timing sA2) (stream_timing sB2).
frp_auto [reference:(sC1); reference:(sA2); reference:(sB2)] [].
Qed.

Proposition T2 : subset_timing (stream_timing sA1) (stream_timing sC1).
Proof Mode "Classic".
rewrite /sC1 /sA2.
apply subset_timing_merge_left.
rewrite stream_timing_snapshot.
rewrite stream_timing_map_s.
apply subset_timing_is_reflective.
Restart.
frp_auto [reference:(sC1); reference:(sA2); reference:(sB2)] [].
Qed.

Proposition T3 : subset_timing (stream_timing sB1) (stream_timing sC1).
frp_auto [reference:(sC1); reference:(sA2); reference:(sB2)] [].
Qed.

End Sample1_Sample1.


