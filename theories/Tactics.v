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

(* 仮定のリストをrewriteする関数 *)
Ltac2 rec frp_rewrite_hypotheses (hyps : constr list) :=
  match hyps with
  | [] => ()
  | h :: rest =>
      (* Message.print (Message.of_string (String.concat "" ["rewrite "; (Message.to_string (Message.of_constr h)); "."])); *)
      (try0 (fun () => do_rewrite h));
      frp_rewrite_hypotheses rest
  end.

(* rewriteを行うパターン *)
Ltac2 rec frp_rewrite () :=
  (match! Control.goal () with
   | context[stream_timing (map_s _ _)] =>
       do_rewrite constr:(stream_timing_map_s);
       frp_rewrite ()
   | context[stream_timing (snapshot _ _ _)] =>
       do_rewrite constr:(stream_timing_snapshot);
       frp_rewrite ()
   | context[stream_timing (merge (never _) _ _)] =>
       do_rewrite constr:(stream_timing_merge_never_left);
       frp_rewrite ()
   | context[stream_timing (merge _ (never _) _)] =>
       do_rewrite constr:(stream_timing_merge_never_right);
       frp_rewrite ()
   | context[cell_timing (hold _ _)] =>
       do_rewrite constr:(cell_timing_hold);
       frp_rewrite ()
   | context[cell_timing (map_c _ _)] =>
       do_rewrite constr:(cell_timing_map_c);
       frp_rewrite ()
   | context[cell_timing (apply (constant _) _)] =>
       do_rewrite constr:(cell_timing_apply_constant_left);
       frp_rewrite ()
   | context[cell_timing (apply _ (constant _))] =>
       do_rewrite constr:(cell_timing_apply_constant_right);
       frp_rewrite ()
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

(* applyを行うパターン *)
Ltac2 rec frp_apply () :=
  (match! Control.goal () with
   | context[same_timing ?_a ?_a] =>
       do_apply constr:(same_timing_is_reflective);
       Control.enter (fun () => frp_apply ())
   | context[same_timing _ _] =>
       do_apply constr:(same_timing_is_transitive);
       Control.enter (fun () => frp_apply ())
   | context[subset_timing ?_a ?_a] =>
       do_apply constr:(subset_timing_is_reflective);
       Control.enter (fun () => frp_apply ())
   | context[subset_timing _ _] =>
       do_apply constr:(subset_timing_is_transitive);
       Control.enter (fun () => frp_apply ())
   | context[subset_timing (stream_timing (filter _ _)) (stream_timing _)] =>
       do_apply constr:(filter_subset_timing);
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

(* バックトラックが必要なパターン *)
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
     | subset_timing _ (cell_timing (apply _ _)) =>
         plus
           (fun () =>
             do_apply constr:(subset_timing_apply_left);
             repeat_core_tactics ();
             handle_special_patterns ())
           (fun _ =>
             do_apply constr:(subset_timing_apply_right);
             repeat_core_tactics ();
             handle_special_patterns ())
     (* それ以外の場合はエラーを出して、バックトラックを行う *)
    | _ => backtrack_tactic_failure "frp_auto: backtracking"
     end)
  else
    ().

Ltac2 frp_auto (defs : reference list) (hyps : constr list) : unit :=
  (* frp_unfoldを実行 *)
  (Message.print (Message.of_string "frp_auto: unfolding definitions..."));
  (try0 (fun () => frp_unfold defs));
  
  (* 仮定をrewriteする *)
  Message.print (Message.of_string "frp_auto: rewriting hypotheses...");
  frp_rewrite_hypotheses hyps;

  (* liftやgateといった複数プリミティブで構成される要素を展開 *)
  Message.print (Message.of_string "frp_auto: unfold definitions...");
  unfold lift;
  unfold gate;
  
  (* コアタクティックを繰り返し実行 *)
  Message.print (Message.of_string "frp_auto: repeating core tactics...");
  repeat_core_tactics ();
  
  (* ゴールがなくなったら終了 *)
  if Int.equal (Control.numgoals ()) 0 then () else
  
  (* merge, applyなどのバックトラックが必要なパターンを処理 *)
  Message.print (Message.of_string "frp_auto: handling special patterns...");
  handle_special_patterns ().








