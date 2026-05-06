From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition isizeasSubAssignREFisize_sub_assign_lemma (π : thread_id) : Prop :=
  ∀ (isizeasSubAssign_sub_assign_loc : loc) , 
  isizeasSubAssign_sub_assign_loc ◁ᵥ{π, MetaNone} isizeasSubAssign_sub_assign_loc @ function_ptr [PtrSynType; (IntSynType ISize)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_isizeasSubAssign_sub_assign (RRGS:=RRGS)   <LFT> late_lft_0 <INST!>) (λ π, (True))%I) -∗
  typed_function π (isizeasSubAssignREFisize_sub_assign_def isizeasSubAssign_sub_assign_loc  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_isizeasSubAssignREFisize_sub_assign  <LFT> ulft_1 <LFT> ulft_2 <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_isizeasSubAssignREFisize_sub_assign <LFT> ulft_1 <LFT> ulft_2 <INST!>)%Z⌝))).
End proof.

Ltac isizeasSubAssignREFisize_sub_assign_prelude :=
  unfold isizeasSubAssignREFisize_sub_assign_lemma;
  set (FN_NAME := FUNCTION_NAME "isizeasSubAssignREFisize_sub_assign");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  start_function "isizeasSubAssignREFisize_sub_assign" ϝ ( [ulft_1 [ulft_2 [] ] ] ) ( [] ) ( ? ) (  );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
