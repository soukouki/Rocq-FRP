
From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.

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

Lemma subset_timing_merge_left a (t1 : timing) (s1 s2 : stream a) (f : a -> a -> a) :
  subset_timing t1 (stream_timing s1) ->
  subset_timing t1 (stream_timing (merge s1 s2 f)).
Proof.
move => H1.
apply subset_timing_is_transitive with (b := stream_timing s1) => //.
by apply merge_subset_timing_left.
Qed.
Hint Resolve subset_timing_merge_left : frp.

Lemma subset_timing_merge_right a (t1 : timing) (s1 s2 : stream a) (f : a -> a -> a) :
  subset_timing t1 (stream_timing s2) ->
  subset_timing t1 (stream_timing (merge s1 s2 f)).
Proof.
move => H1.
apply subset_timing_is_transitive with (b := stream_timing s2) => //.
by apply merge_subset_timing_right.
Qed.
Hint Resolve subset_timing_merge_right : frp.

Section Sample1_Sample1.

Variable a : Type.

Variable sA1 : stream a.
Variable sB1 : stream a.
Variable cFlag : cell a.

Hypothesis Hy1 : different_timing (stream_timing sA1) (stream_timing sB1).

Variable f1 : a -> a.
Variable f2 : a -> a -> a.
Definition sA2 := snapshot f2 (map_s f1 sA1) cFlag.
Hint Unfold sA2 : frp.

Variable f3 : a -> a -> a.
Definition sB2 := merge sB1 (never a) f3.
Hint Unfold sB2 : frp.

Variable f4 : a -> a -> a.
Definition sC1 := merge sA2 sB2 f4.
Hint Unfold sC1 : frp.

Theorem T1 : different_timing (stream_timing sA2) (stream_timing sB2).
autounfold with frp.
autorewrite with frp.
eauto with frp.
Qed.

Theorem T2 : subset_timing (stream_timing sA1) (stream_timing sC1).
rewrite /sC1.
rewrite /sA2 /sB2.
apply subset_timing_is_transitive with (b := stream_timing (snapshot f2 (map_s f1 sA1) cFlag)).
- rewrite stream_timing_snapshot.
  by rewrite stream_timing_map_s.
- by apply merge_subset_timing_left.
Restart.
autounfold with frp.
auto with frp. (* 何も起こらない！ *)
Restart.
autounfold with frp.
auto with frp.
have : subset_timing (stream_timing sA1) (stream_timing (snapshot f2 (map_s f1 sA1) cFlag)).
  by autorewrite with frp.
auto with frp.
Qed.

Theorem T3 : subset_timing (stream_timing sB1) (stream_timing sC1).
rewrite /sC1.
rewrite /sA2 /sB2.
apply subset_timing_is_transitive with (b := stream_timing (merge sB1 (never a) f3)).
- by rewrite stream_timing_merge_never_right.
- by apply merge_subset_timing_right.
Qed.

End Sample1_Sample1.


