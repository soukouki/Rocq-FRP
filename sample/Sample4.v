Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.

(* 
// applyを含む例
public class Test4 {
	Cell<Integer> cOut;
	public Test4(Cell<Lambda1<Integer, Integer>> cFunc, Cell<Integer> cValue) {
		cOut = cFunc.apply(cValue);
		// check(subset_timing(cFunc, cOut))
		// check(subset_timing(cValue, cOut))
	}
}
 *)

Section Sample4_Sample4.

Variable a : Type.

Variable cOut : cell a.

Variable cFunc : cell (a -> a).
Variable cValue : cell a.

Hypothesis Hy1 : cOut = apply cFunc cValue.

Theorem T1 : subset_timing (cell_timing cFunc) (cell_timing cOut).
Proof.
rewrite Hy1.
apply subset_timing_apply_left.
apply subset_timing_is_reflective.
Qed.

Theorem T2 : subset_timing (cell_timing cValue) (cell_timing cOut).
Proof.
rewrite Hy1.
apply subset_timing_apply_right.
apply subset_timing_is_reflective.
Qed.

End Sample4_Sample4.
