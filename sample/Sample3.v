Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.

(* 
// lift, constantを含む例
public class Test3 {
	Cell<Integer> cOut;
	public Test3(Cell<Integer> cIn) {
		cOut = cIn.lift(new Cell<Int>(10) , (i, ten) -> i * ten);
		// check(same_timing(sAdd, cOut))
	}
}
 *)

Section Sample3_Sample3.

Variable a : Type.

Variable cOut : cell a.

Variable cIn : cell a.

Variable v1 : a.
Variable f1 : a -> a -> a.
Hypothesis Hy1 : cOut = lift cIn (constant v1) f1.

Theorem T1 : same_timing (cell_timing cIn) (cell_timing cOut).
Proof.
rewrite Hy1.
rewrite /lift.
rewrite cell_timing_apply_constant_right.
by rewrite cell_timing_map_c.
Qed.

End Sample3_Sample3.
