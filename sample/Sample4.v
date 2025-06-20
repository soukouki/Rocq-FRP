Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing Tactics.

Set Default Proof Mode "Ltac2".

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

Proposition T1 : subset_timing (cell_timing cFunc) (cell_timing cOut).
Proof.
frp_auto [] [constr:(Hy1)].
Qed.

Proposition T2 : subset_timing (cell_timing cValue) (cell_timing cOut).
Proof.
frp_auto [] [constr:(Hy1)].
Qed.

End Sample4_Sample4.
