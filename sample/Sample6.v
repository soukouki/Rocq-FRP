Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing Tactics.

Set Default Proof Mode "Ltac2".

(* 
public class Test6 {
	Stream<Integer> sOut;
	public Test6(Stream<Integer> sIn) {
		sOut = helper(sIn);
		// hypothesis(same_timing(sIn, sOut))
		// check(same_timing(sIn, sOut))
	}
	public static Stream<Integer> helper(Stream<Integer> sIn) {
		return sIn.map(n -> n + 1);
	}
}
 *)

Section Sample6_Sample6.

Variable a : Type.

Variable sOut : stream a.

Variable sIn : stream a.

(* sOut = helper(sIn); については、helperという関数呼び出しが入っているので翻訳しない *)

Hypothesis Hy1 : same_timing (stream_timing sIn) (stream_timing sOut).

Proposition T1 : same_timing (stream_timing sIn) (stream_timing sOut).
Proof.
frp_auto [] [].
Qed.

End Sample6_Sample6.
