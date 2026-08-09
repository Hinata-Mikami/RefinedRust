From refinedrust Require Import typing.
From rrstd.closures.theories Require Export simplification.


Definition FnOnce_Params_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) :=
  (Type).
Definition FnOnce_Pre_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) :=
  (thread_id → FnOnce_Params → (RT_xt (Self_rt)) → (RT_xt (Args_rt)) → iProp Σ).
Definition FnOnce_Post_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) (FnOnce_Pre: (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params))) :=
(thread_id → FnOnce_Params → (RT_xt (Self_rt)) → (RT_xt (Args_rt)) → (RT_xt (Output_rt)) → iProp Σ).
Definition FnOnce_PostMut_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) (FnOnce_Pre: (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params))) (FnOnce_Post: (FnOnce_Post_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre))) :=
  (thread_id → FnOnce_Params → (RT_xt (Self_rt)) → (RT_xt (Args_rt)) → (RT_xt (Self_rt)) → (RT_xt (Output_rt)) → iProp Σ).
Definition FnOnce_PanicCondition_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) (FnOnce_Pre: (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params))) (FnOnce_Post: (FnOnce_Post_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre))) (FnOnce_PostMut: (FnOnce_PostMut_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre) (FnOnce_Post))) :=
  ((RT_xt (Self_rt)) → FnOnce_Params → (RT_xt (Args_rt)) → Prop).
Record FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{Output_rt : !RT} : Type := mk_FnOnce_spec_attrs {
  FnOnce_Params  : (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt));
  FnOnce_Pre  : (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params));
  FnOnce_Post  : (FnOnce_Post_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre));
  FnOnce_PostMut  : (FnOnce_PostMut_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre) (FnOnce_Post));
  FnOnce_PanicCondition : (FnOnce_PanicCondition_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre) (FnOnce_Post) (FnOnce_PostMut));
}.

#[global] Arguments FnOnce_spec_attrs : clear implicits.
#[global] Arguments FnOnce_spec_attrs {_ _}.
#[global] Arguments mk_FnOnce_spec_attrs  {_} {_} {_} {_} {_}.

Definition closure_may_panic {Self Params Args : Type}
    (PanicCondition : Self → Params → Args → Prop) : Prop :=
  ∃ self params args, PanicCondition self params args.

(* Unfold this in solve_goal *)
Global Hint Unfold closure_may_panic : solve_goal_unfold.

Section automation.
  Context `{RRGS : !refinedrustGS Σ}.

  (* Finding generic closure preconditions *)
  Definition FindClosurePre {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π self args :=
    {| fic_A := FnOnce_Params A;
       fic_Prop p := FnOnce_Pre A π p self args |}.
  Global Typeclasses Opaque FindClosurePre.

  Global Instance related_to_closure_pre {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args :
    RelatedTo (FnOnce_Pre A π p self args) | 100 :=
      {| rt_fic := FindClosurePre A π self args |}.

  (* TODO: maybe make this instantiation modulo universal quantifier instantiation and persistence modality *)
  Lemma find_in_context_closure_pre {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π self args T :
    (∃ p, FnOnce_Pre A π p self args ∗ T p)
    ⊢ find_in_context (FindClosurePre A π self args) T.
  Proof.
    rewrite /FindClosurePre/find_in_context.
    iIntros "(%x & Hpre & HT)".
    iFrame.
  Qed.
  Definition find_in_context_closure_pre_inst := [instance @find_in_context_closure_pre with FICSyntactic].
  Global Existing Instance find_in_context_closure_pre_inst.

  Lemma subsume_closure_pre {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p1 p2 self1 self2 args1 args2 T :
    ⌜p1 = p2⌝ ∗ ⌜self1 = self2⌝ ∗ ⌜args1 = args2⌝ ∗ T
    ⊢ subsume (FnOnce_Pre A π p1 self1 args1) (FnOnce_Pre A π p2 self2 args2) T.
  Proof.
    iIntros "(<- & <- & <- & $)".
    eauto.
  Qed.
  Definition subsume_closure_pre_inst := [instance @subsume_closure_pre].
  Global Existing Instance subsume_closure_pre_inst.

  (* Finding generic closure postconditions *)
  Definition FindClosurePost {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args :=
    {| fic_A := RT_xt Output_rt;
       fic_Prop out := FnOnce_Post A π p self args out |}.
  Global Typeclasses Opaque FindClosurePost.

  Global Instance related_to_closure_post {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args out :
    RelatedTo (FnOnce_Post A π p self args out) | 100 :=
      {| rt_fic := FindClosurePost A π p self args |}.

  Lemma find_in_context_closure_post {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args T :
    (∃ out, FnOnce_Post A π p self args out ∗ T out)
    ⊢ find_in_context (FindClosurePost A π p self args) T.
  Proof.
    rewrite /FindClosurePost/find_in_context.
    iIntros "(%x & Hpost & HT)".
    iFrame.
  Qed.
  Definition find_in_context_closure_post_inst := [instance @find_in_context_closure_post with FICSyntactic].
  Global Existing Instance find_in_context_closure_post_inst.

  Lemma subsume_closure_post {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args out1 out2 T :
    ⌜out1 = out2⌝ ∗ T
    ⊢ subsume (FnOnce_Post A π p self args out1) (FnOnce_Post A π p self args out2) T.
  Proof.
    iIntros "(<- & $)".
    eauto.
  Qed.
  Definition subsume_closure_post_inst := [instance @subsume_closure_post].
  Global Existing Instance subsume_closure_post_inst.

  (* Finding generic closure postconditions (mut) *)
  Definition FindClosurePostMut {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args :=
    {| fic_A := RT_xt Self_rt * RT_xt Output_rt;
       fic_Prop '(self', out) := FnOnce_PostMut A π p self args self' out |}.
  Global Typeclasses Opaque FindClosurePostMut.

  Global Instance related_to_closure_post_mut {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args self' out :
    RelatedTo (FnOnce_PostMut A π p self args self' out) | 100 :=
      {| rt_fic := FindClosurePostMut A π p self args |}.

  Lemma find_in_context_closure_post_mut {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args T :
    (∃ self' out, FnOnce_PostMut A π p self args self' out ∗ T (self', out))
    ⊢ find_in_context (FindClosurePostMut A π p self args) T.
  Proof.
    rewrite /FindClosurePostMut/find_in_context.
    iIntros "(%x & %y & Hpost & HT)".
    iFrame.
  Qed.
  Definition find_in_context_closure_post_mut_inst := [instance @find_in_context_closure_post_mut with FICSyntactic].
  Global Existing Instance find_in_context_closure_post_mut_inst.

  Lemma subsume_closure_post_mut {Self_rt Args_rt Output_rt : RT}
    (A : FnOnce_spec_attrs Self_rt Args_rt Output_rt)
    π p self args self'1 self'2 out1 out2 T :
    ⌜self'1 = self'2⌝ ∗ ⌜out1 = out2⌝ ∗ T
    ⊢ subsume (FnOnce_PostMut A π p self args self'1 out1) (FnOnce_PostMut A π p self args self'2 out2) T.
  Proof.
    iIntros "(<- & <- & $)".
    eauto.
  Qed.
  Definition subsume_closure_post_mut_inst := [instance @subsume_closure_post_mut].
  Global Existing Instance subsume_closure_post_mut_inst.
End automation.


Section closure_props.
  Context `{!refinedrustGS Σ}.
  Context (Clos_rt Args_rt Clos_out_rt : RT).

  Class ClosureHasTrivialPre (fnonce_attrs : FnOnce_spec_attrs Clos_rt Args_rt Clos_out_rt) := closure_has_trivial_pre_proof :
    ∀ π self args, ⊢ ∃ p, FnOnce_Pre fnonce_attrs π p self args.

End closure_props.

Ltac solve_closure_has_trivial_pre :=
  match goal with
  | |- ClosureHasTrivialPre _ _ _ _ =>
    unfold ClosureHasTrivialPre;
    intros ???; prepare_initial_coq_context;
    iStartProof;
    unshelve (repeat liRStep; solve[fail]);
    unshelve (sidecond_solver);
    sidecond_hammer;
    apply inhabitant
  end.

(* TODO: don't have this as hint, but generate instances in the frontend *)
Global Hint Extern 100 (ClosureHasTrivialPre _ _ _ _) =>
  solve_closure_has_trivial_pre : typeclass_instances.
