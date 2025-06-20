Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing Tactics.

Set Default Proof Mode "Ltac2".

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

Proposition T1 : subset_timing (stream_timing sOut) (stream_timing sIn).
Proof.
frp_auto [] [constr:(Hy1)].
Qed.

End Sample5_Sample5.
