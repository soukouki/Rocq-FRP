Set Implicit Arguments.

From Stdlib Require Import ssreflect.
From CoqFRP Require Import FRP Timing.
From Ltac2 Require Import Ltac2.

Ltac2 test_ () :=
  try (rewrite stream_timing_snapshot).
Ltac2 Notation test := test_ ().
