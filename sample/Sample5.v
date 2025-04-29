Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.

(* 
// filterを含む例
public class Test5 {
	Stream<Integer> sOut;
	public Test5(Stream<Integer> sIn, Cell<Boolean> cIn) {
		sOut = sIn.gate(cIn); // gateはsnapshotとfilterを組み合わせたプリミティブ
		// check(subset_timing(sOut, sIn))
	}
}
 *)

Section Sample5_Sample5.

Variable a : Type.

Variable sOut : stream a.

Variable sIn : stream a.
Variable cIn : cell bool.

Hypothesis Hy1 : sOut = gate sIn cIn.

Theorem T1 : subset_timing (stream_timing sOut) (stream_timing sIn).
Proof.
rewrite Hy1 /gate.
rewrite stream_timing_map_s.
apply filter_subset_timing.
by rewrite stream_timing_snapshot.
Qed.

End Sample5_Sample5.
