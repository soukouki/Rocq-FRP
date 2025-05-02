Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.

(* 
// セルループを含む例
public class Sample2 {
	CellLoop<Integer> cSum;
	public Sample2(Stream<Integer> sAdd) {
		cSum = new CellLoop<Integer>();
		cSum.loop(sAdd.snapshot(cSum, (a, s) -> a + s).hold(0));
		// check(same_timing(sAdd, cSum))
	}
}
 *)

Section Sample2_Sample2.

Variable a : Type.

Variable cSum : cell a.

Variable sAdd : stream a.

Variable f1 : a -> a -> a.
Variable v1 : a.
Hypothesis Hy1 : cSum = hold v1 (snapshot f1 sAdd cSum).

Theorem T1 : same_timing (stream_timing sAdd) (cell_timing cSum).
Admitted.

End Sample2_Sample2.
