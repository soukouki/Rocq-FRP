Set Implicit Arguments.

From CoqFRP Require Import FRP Timing.

From Ltac2 Require Import Ltac2 Control Std List Message String.

Ltac2 frp_unfold (defs : reference list) :=
  (* Message.print (Message.of_string "unfold"); *)
  let clause_concl := { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences } in
  Std.unfold (List.map (fun r => (r, AllOccurrences)) defs) clause_concl.

(* rewrite実行関数 *)
Ltac2 do_rewrite (eq_name : constr) :=
  (* Message.print (Message.of_string (String.concat "" ["rewrite "; (Message.to_string (Message.of_constr eq_name)); "."])); *)
  let evar_flag := false in
  let rewriting_list := [
    {
      rew_orient := None;
      rew_repeat := Precisely 1;
      rew_equatn := fun () => (eq_name, NoBindings)
    }
  ] in
  let clause := {
    on_hyps := None;
    on_concl := AllOccurrences
  } in
  let after_tac := None in
  Std.rewrite evar_flag rewriting_list clause after_tac.

(* rewrite用関数 *)
Ltac2 rec frp_rewrite () :=
  (* stream_timing (map ...) パターンの処理 *)
  (match! Control.goal () with
   | context[stream_timing (map_s _ _)] =>
       do_rewrite constr:(stream_timing_map_s);
       frp_rewrite ()
   (* stream_timing (snapshot ...) パターンの処理 *)
   | context[stream_timing (snapshot _ _ _)] =>
       do_rewrite constr:(stream_timing_snapshot);
       frp_rewrite ()  (* 再帰的に続行 *)
   (* stream_timing (merge (never _) _ _) パターンの処理 *)
   | context[stream_timing (merge (never _) _ _)] =>
       do_rewrite constr:(stream_timing_merge_never_left);
       frp_rewrite ()  (* 再帰的に続行 *)
   (* stream_timing (merge _ (never _) _) パターンの処理 *)
   | context[stream_timing (merge _ (never _) _)] =>
       do_rewrite constr:(stream_timing_merge_never_right);
       frp_rewrite ()  (* 再帰的に続行 *)
   (* cell_timing (hold _ _) パターンの処理 *)
   | context[cell_timing (hold _ _)] =>
       do_rewrite constr:(cell_timing_hold);
       frp_rewrite ()  (* 再帰的に続行 *)
   (* cell_timing (map_c _ _) パターンの処理 *)
   | context[cell_timing (map_c _ _)] =>
       do_rewrite constr:(cell_timing_map_c);
       frp_rewrite ()  (* 再帰的に続行 *)
   (* cell_timing (apply (constant _) _) パターンの処理 *)
   | context[cell_timing (apply (constant _) _)] =>
       do_rewrite constr:(cell_timing_apply_constant_left);
       frp_rewrite ()  (* 再帰的に続行 *)
   (* cell_timing (apply _ (constant _)) パターンの処理 *)
   | context[cell_timing (apply _ (constant _))] =>
       do_rewrite constr:(cell_timing_apply_constant_right);
       frp_rewrite ()  (* 再帰的に続行 *)
   | _ => ()
   end).

(* apply実行関数 *)
Ltac2 do_apply (lemma_name : constr) :=
  (* Message.print (Message.of_string (String.concat "" ["apply "; (Message.to_string (Message.of_constr lemma_name)); "."])); *)
  let advanced_flag := false in
  let evar_flag := false in
  let constr_with_bindings_list := [fun () => (lemma_name, NoBindings)] in
  let intro_pattern_option := None in
  Std.apply advanced_flag evar_flag constr_with_bindings_list intro_pattern_option.

(* apply用関数 *)
Ltac2 rec frp_apply () :=
  (* same_timing関数への反射性の適用 *)
  (match! Control.goal () with
   | context[same_timing ?_a ?_a] =>
       do_apply constr:(same_timing_is_reflective);
       (* ゴールが残っている場合のみ再帰的に続行 *)
       Control.enter (fun () => frp_apply ())
   (* same_timing関数への推移性の適用 *)
   | context[same_timing _ _] =>
       do_apply constr:(same_timing_is_transitive);
       (* ゴールが残っている場合のみ再帰的に続行 *)
       Control.enter (fun () => frp_apply ())
   (* subset_timing関数への反射性の適用 *)
   | context[subset_timing ?_a ?_a] =>
       do_apply constr:(subset_timing_is_reflective);
       (* ゴールが残っている場合のみ再帰的に続行 *)
       Control.enter (fun () => frp_apply ())
   (* subset_timing関数への推移性の適用 *)
   | context[subset_timing _ _] =>
       do_apply constr:(subset_timing_is_transitive);
       (* ゴールが残っている場合のみ再帰的に続行 *)
       Control.enter (fun () => frp_apply ())
   | _ => ()
   end).

Ltac2 frp_trivial() :=
  (* Message.print (Message.of_string "trivial"); *)
  trivial.

(* ゴールが変化したかチェックする関数 *)
Ltac2 goal_changed (old_goal : constr) : bool :=
  if Int.gt (Control.numgoals ()) 0 then
    Bool.neg (Constr.equal old_goal (Control.goal ()))
  else
    true.

(* frp_rewrite, frp_apply, frp_trivialを繰り返し実行する関数 *)
Ltac2 rec repeat_core_tactics () : unit :=
  if Int.gt (Control.numgoals ()) 0 then
    let old_goal := Control.goal () in
    (* frp_rewriteを実行 *)
    (try0 frp_rewrite);
    (* ゴールがなくなったら終了 *)
    if Int.equal (Control.numgoals ()) 0 then () else
    (* frp_applyを実行 *)
    (try0 frp_apply);
    (* ゴールがなくなったら終了 *)
    if Int.equal (Control.numgoals ()) 0 then () else
    (* frp_trivialを実行 *)
    (try0 frp_trivial);
    (* ゴールがなくなったら終了 *)
    if Int.equal (Control.numgoals ()) 0 then () else
    (* ゴールが変化した場合は繰り返し *)
    if goal_changed old_goal then
      repeat_core_tactics ()
    else
      ()
  else
    ().

Ltac2 rec handle_special_patterns () : unit :=
  if Int.gt (Control.numgoals ()) 0 then
    (* subset_timing t1 (stream_timing (merge s1 s2 f)) パターンの処理 *)
    (match! Control.goal () with
     | subset_timing _ (stream_timing (merge _ _ _)) =>
         plus
           (fun () =>
             do_apply constr:(subset_timing_merge_left);
             repeat_core_tactics ();
             handle_special_patterns ())
           (fun _ =>
             do_apply constr:(subset_timing_merge_right);
             repeat_core_tactics ();
             handle_special_patterns ())
     (* subset_timing t1 (cell_timing (apply cf cp)) パターンの処理 *)
     | context[subset_timing _ (cell_timing (apply _ _))] =>
         plus
           (fun () =>
             do_apply constr:(subset_timing_apply_left);
             repeat_core_tactics ();
             handle_special_patterns ())
           (fun _ =>
             do_apply constr:(subset_timing_apply_right);
             repeat_core_tactics ();
             handle_special_patterns ())
     end)
  else
    ().

Ltac2 frp_auto (defs : reference list) : unit :=
  (* 1. frp_unfoldを実行 *)
  (try0 (fun () => frp_unfold defs));
  
  (* ゴールがなくなったら終了 *)
  if Int.equal (Control.numgoals ()) 0 then () else
  
  (* 2-5. コアタクティックを繰り返し実行 *)
  repeat_core_tactics ();
  
  (* ゴールがなくなったら終了 *)
  if Int.equal (Control.numgoals ()) 0 then () else
  
  (* 6-7. 特定パターンの処理 *)
  handle_special_patterns ().
