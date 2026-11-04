From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.theories Require Export closures.
From rrstd.closures.closures Require Export generated_code_closures generated_specs_closures.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFmutFasFnOnceA_call_once_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(F_rt : !RT) `(FnOnce_F_A_Output_rt : !RT) `(A_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_A_Output_st : !syn_type) `(FnOnce_F_A_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnOnce_F_A_realization : !(trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) `(FnMut_F_A_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnMut_F_A_realization : !(trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) `(DropGlue_FasFnOnceA_Output_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) `(DropGlue_FasFnOnceA_Output_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_call_mut_loc : loc) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (FnOnce_F_A_Output_st) →
  FnMut_F_A_call_mut_loc ◁ᵥ{π, MetaNone} FnMut_F_A_call_mut_loc @ function_ptr [RefSynType; A_st] (<tag_type> spec_collapse_params _ _ (λ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt; FnOnce_F_A_Output_rt] : list RT), fn_spec_add_late_pre ((FnMut_call_mut_spec (RRGS:=RRGS) (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π))%I)) -∗
  typed_function π (REFmutFasFnOnceA_call_once_def FnMut_F_A_call_mut_loc  A_st  F_st  FnOnce_F_A_Output_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), fn_spec_add_late_pre (type_of_REFmutFasFnOnceA_call_once A_rt F_rt FnOnce_F_A_Output_rt A_st F_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_A_spec_attrs DropGlue_F_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs -[ulft_1] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) (λ π, ((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (((trait_incl_of_REFmutFasFnOnceA_call_once (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnOnce_F_A_realization) (FnMut_F_A_spec_attrs) (FnMut_F_A_realization) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization) (DropGlue_FasFnOnceA_Output_spec_attrs) (DropGlue_FasFnOnceA_Output_realization))-[ulft_1] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) π))).
End proof.

Ltac REFmutFasFnOnceA_call_once_prelude :=
  unfold REFmutFasFnOnceA_call_once_lemma;
  set (FN_NAME := FUNCTION_NAME "REFmutFasFnOnceA_call_once");
  intros A_rt F_rt FnOnce_F_A_Output_rt A_st F_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnOnce_F_A_realization FnMut_F_A_spec_attrs FnMut_F_A_realization DropGlue_A_spec_attrs DropGlue_A_realization DropGlue_F_spec_attrs DropGlue_F_realization DropGlue_FasFnOnceA_Output_spec_attrs DropGlue_FasFnOnceA_Output_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let A_ty := fresh "A_ty" in
  let F_ty := fresh "F_ty" in
  let FnOnce_F_A_Output_ty := fresh "FnOnce_F_A_Output_ty" in
  start_function "REFmutFasFnOnceA_call_once" ϝ fid ( [ulft_1 [] ] ) ( [A_ty [F_ty [FnOnce_F_A_Output_ty [] ] ] ] ) ( ? );
  intros arg_self arg_args;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ <[
      "FnOnce_F_A_Output" :=
  existT _ (FnOnce_F_A_Output_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
