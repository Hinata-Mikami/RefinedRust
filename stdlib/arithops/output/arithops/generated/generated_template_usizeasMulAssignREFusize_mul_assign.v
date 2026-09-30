From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition usizeasMulAssignREFusize_mul_assign_lemma (π : thread_id) : Prop :=
  ∀ (usizeasMulAssign_mul_assign_loc : loc) , 
  usizeasMulAssign_mul_assign_loc ◁ᵥ{π, MetaNone} usizeasMulAssign_mul_assign_loc @ function_ptr [RefSynType; (IntSynType USize)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), let realization := (usizeasMulAssign_realization) in fn_spec_add_late_pre ((MulAssign_mul_assign_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[] -[] -[]))  -[late_lft_0] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[] π))%I) -∗
  typed_function π (usizeasMulAssignREFusize_mul_assign_def usizeasMulAssign_mul_assign_loc  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usizeasMulAssignREFusize_mul_assign -[ulft_1; ulft_2] -[]) (λ π, (True)
  ∗ ((trait_incl_of_usizeasMulAssignREFusize_mul_assign-[ulft_1; ulft_2] -[]) π)
  ∗ ((introduce_direct ((let realization := (usizeasMulAssign_realization) in realization.(trait_ctx_wf) -[] -[] π)))))).
End proof.

Ltac usizeasMulAssignREFusize_mul_assign_prelude :=
  unfold usizeasMulAssignREFusize_mul_assign_lemma;
  set (FN_NAME := FUNCTION_NAME "usizeasMulAssignREFusize_mul_assign");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  start_function "usizeasMulAssignREFusize_mul_assign" ϝ fid ( [ulft_1 [ulft_2 [] ] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("ulft_2", ulft_2) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
