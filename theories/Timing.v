Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List.
From CoqFRP Require Import FRP.

Definition timing := list time.

Definition same_timing (a b : timing) := a = b.

Theorem same_timing_reflective a : same_timing a a.
Proof. by []. Qed.

Theorem same_timing_is_transitive a b c : same_timing a b -> same_timing b c -> same_timing a c.
Proof. move => H1 H2; apply (eq_trans H1 H2). Qed.

Theorem same_timing_is_commutative a b : same_timing a b -> same_timing b a.
Proof. move => H1; symmetry; exact H1. Qed.

Definition different_timing (a b : timing) := forall t, In t a <> In t b.

(* timing(a) ⊂ timing(b) であることを示す *)
Definition subset_timing (a b : timing) := forall t, In t a -> In t b.

Theorem subset_timing_is_reflective a : subset_timing a a.
Proof. by []. Qed.

Theorem subset_timing_is_transitive a b c : subset_timing a b -> subset_timing b c -> subset_timing a c.
Proof. move => H1 H2 t H3; by apply /H2 /H1. Qed.

Definition stream_timing a (s : stream a) : timing := map fst (occs s).

Definition cell_timing a (c : cell a) : timing := map fst (snd (steps c)).

Theorem stream_timing_map_s a b (f : a -> b) (s : stream a) : stream_timing (map_s f s) = stream_timing s.
Admitted.

Theorem stream_timing_snapshot a1 a2 a3 (f : a1 -> a2 -> a3) (s : stream a1) (c : cell a2) : stream_timing (snapshot f s c) = stream_timing s.
Admitted.

Theorem merge_subset_timing_left a (f : a -> a -> a) (s1 s2 : stream a) : subset_timing (stream_timing s1) (stream_timing (merge s1 s2 f)).
Admitted.

Theorem merge_subset_timing_right a (f : a -> a -> a) (s1 s2 : stream a) : subset_timing (stream_timing s2) (stream_timing (merge s1 s2 f)).
Admitted.

Theorem filter_subset_timing a b (f : a -> bool) (s1 : stream a) (s2 : stream b) :
  same_timing (stream_timing s1) (stream_timing s2) ->
  subset_timing (stream_timing (filter f s1)) (stream_timing s2).
Admitted.

Theorem hold_subset_timing a (a0 : a) (s : stream a) (t : time) : subset_timing (cell_timing (hold a0 s t)) (stream_timing s).
Admitted.

Theorem cell_timing_map_c a b (f : a -> b) (c : cell a) : cell_timing (map_c f c) = cell_timing c.
Admitted.

Theorem apply_subset_timing_left a b (c1 : cell (a -> b)) (c2 : cell a) : subset_timing (cell_timing c1) (cell_timing (apply c1 c2)).
Admitted.

Theorem apply_subset_timing_right a b (c1 : cell (a -> b)) (c2 : cell a) : subset_timing (cell_timing c2) (cell_timing (apply c1 c2)).
Admitted.

Theorem occs_eq_to_timing_eq a (s1 s2 : stream a) : occs s1 = occs s2 -> stream_timing s1 = stream_timing s2.
Proof. move => H1; by rewrite /stream_timing H1. Qed.

Theorem cell_timing_apply_constant_right a b (a1 : a) (c : cell (a -> b)) :
  cell_timing (apply c (constant a1)) = cell_timing c.
Admitted.

Theorem cell_timing_apply_constant_left a b (f1 : a -> b) (c : cell a) :
  cell_timing (apply (constant f1) c) = cell_timing c.
Admitted.












