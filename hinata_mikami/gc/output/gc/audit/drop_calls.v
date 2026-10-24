From radium Require Import lang notation.
From refinedrust.examples.gc.generated Require Import generated_code_gc.
Open Scope expr_scope.

(** A conservative observer of an EXISTING Radium statement transition.
    It cannot record an arbitrary ghost event: entering a callee requires
    the original operational step, including function resolution and arguments.
    This is a small semantic building block, not a trace theorem for sweep. *)
Record call_entry := CallEntry {
  entry_callee : val;
  entry_arguments : list expr;
}.

Definition call_observation (s : stmt) (result : runtime_expr) : option call_entry :=
  match s, result with
  | Call (Val vf) args _ _ _, CallFrame _ _ _ _ _ _ =>
      Some (CallEntry vf args)
  | _, _ => None
  end.

Section observer.
Context `{RC : RadiumConfig}.

Definition observed_stmt_step s π caller σ κ event result σ' spawned : Prop :=
  stmt_step s π caller σ κ result σ' spawned ∧
  event = call_observation s result.

Lemma observed_step_erases s π caller σ κ event result σ' spawned :
  observed_stmt_step s π caller σ κ event result σ' spawned →
  stmt_step s π caller σ κ result σ' spawned.
Proof. by intros [Hstep _]. Qed.

Lemma every_step_has_unique_observation s π caller σ κ result σ' spawned :
  stmt_step s π caller σ κ result σ' spawned →
  exists! event, observed_stmt_step s π caller σ κ event result σ' spawned.
Proof.
  intros Hstep. exists (call_observation s result). split; first done.
  by intros event [_ ->].
Qed.

Lemma observed_call_resolves vf vs destination normal unwind π caller σ κ
    result σ' spawned :
  observed_stmt_step (Call (Val vf) (Val <$> vs) destination normal unwind)
    π caller σ κ (Some (CallEntry vf (Val <$> vs))) result σ' spawned →
  ∃ a fn,
    val_to_loc vf = Some (fn_loc a) ∧ σ.(st_fntbl) !! a = Some fn ∧
    result = CallFrame π caller destination normal unwind
      (to_rtstmt π fn (Goto fn.(f_init))).
Proof.
  intros [Hstep Hevent]. inversion Hstep; subst; simpl in Hevent;
    try discriminate. eauto 8.
Qed.
End observer.

(** Separate, STATIC certificates about the actual generated CFG.
    They follow normal call continuations, not callee bodies or unwinding.
    They do not assert that a run exists, terminates, or physically frees memory. *)
Record call_site := CallSite {
  site_callee : expr;
  site_arguments : list expr;
  site_destination : option (order * op_type * expr);
}.

Fixpoint normal_calls_until (fuel : nat) (code : gmap label stmt)
    (stop : label) (s : stmt) : option (list call_site) :=
  match fuel with
  | O => None
  | S fuel =>
      match s with
      | Goto b =>
          if decide (b = stop) then Some []
          else code !! b ≫= normal_calls_until fuel code stop
      | Call f args dest normal _ =>
          (cons (CallSite f args dest)) <$> normal_calls_until fuel code stop normal
      | Assign _ _ _ _ rest | Free _ _ _ rest | SkipS rest | ExprS _ rest
      | LocalLive _ _ rest | LocalDead _ rest =>
          normal_calls_until fuel code stop rest
      | _ => None
      end
  end.

Fixpoint assignments_before_call (s : stmt) : option (list (op_type * expr * expr)) :=
  match s with
  | Call _ _ _ _ _ => Some []
  | Assign _ ot lhs rhs rest =>
      (cons (ot, lhs, rhs)) <$> assignments_before_call rest
  | SkipS rest | ExprS _ rest | LocalLive _ _ rest | LocalDead _ rest =>
      assignments_before_call rest
  | _ => None
  end.

Section generated_sweep.
Context `{!LayoutAlg}.
Variables raw setmark len remove drop panic index : loc.

Local Definition sweep_code :=
  (Heap_sweep_def raw setmark len remove drop panic index).(f_code).

Lemma sweep_dead_branch_calls :
  (site_callee <$> default []
    (normal_calls_until 128 sweep_code "_bb2" (Goto "_bb8"))) =
  [Val (l2v remove); Val (l2v raw); Val (l2v drop)].
Proof. reflexivity. Qed.

Lemma sweep_live_branch_calls :
  (site_callee <$> default []
    (normal_calls_until 128 sweep_code "_bb2" (Goto "_bb6"))) =
  [Val (l2v setmark)].
Proof. reflexivity. Qed.

Lemma sweep_from_raw_uses_selected_pointer :
  assignments_before_call (default StuckS (sweep_code !! "_bb9")) =
    Some [(PtrOp, SkipE (SkipE (Var "__21")), copy{ PtrOp } ("node_ptr"))].
Proof. reflexivity. Qed.

(** The Box constructed from node_ptr is placed in __20, and precisely that
    local Box slot is passed to drop glue. The slot is not the Node allocation. *)
Lemma sweep_from_raw_and_drop_share_box_slot :
  normal_calls_until 128 sweep_code "_bb2" (Goto "_bb9") = Some [
    CallSite (Val (l2v raw)) [move{ PtrOp } ("__21")]
      (Some (Na1Ord, use_op_alg' (Box_sls Node_st Global_sls), Var "__20"));
    CallSite (Val (l2v drop)) [&raw{ PRef, Mut } ("__20")] None].
Proof. reflexivity. Qed.

(** Regression check: replacing the generated Drop block by a jump removes
    one call and is rejected by the three-call certificate above. *)
Local Definition without_drop := <["_bb10" := Goto "_bb11"]> sweep_code.

Lemma sweep_without_drop_has_two_calls :
  length (default []
    (normal_calls_until 128 without_drop "_bb2" (Goto "_bb8"))) = 2%nat.
Proof. reflexivity. Qed.

Lemma sweep_without_drop_rejected :
  length (default []
    (normal_calls_until 128 without_drop "_bb2" (Goto "_bb8"))) ≠ 3%nat.
Proof. rewrite sweep_without_drop_has_two_calls. lia. Qed.

End generated_sweep.
