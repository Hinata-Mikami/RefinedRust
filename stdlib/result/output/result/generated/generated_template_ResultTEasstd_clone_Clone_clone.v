From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.theories Require Export result.
From rrstd.result.result Require Export generated_code_result generated_specs_result.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition ResultTEasstd_clone_Clone_clone_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(Clone_T_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) `(Clone_T_realization : !(trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt))))) `(Clone_E_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) `(Clone_E_realization : !(trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (E_rt))))) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_E_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (E_rt) )) `(DropGlue_E_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt))))) (Clone_E_clone_loc : loc) (Clone_T_clone_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (E_st) →
  syn_type_is_layoutable (((Result_els (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (T_st) (E_st)) : syn_type)) →
  Clone_E_clone_loc ◁ᵥ{π, MetaNone} Clone_E_clone_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (Clone_E_lfts_inst : prod_vec lft Clone_E_realization.(trait_ctx_lfts)) (Clone_E_tys_inst : plist type Clone_E_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[E_ty]) : ([E_rt] : list RT), fn_spec_add_late_pre ((Clone_clone_spec (RRGS:=RRGS) (Clone_E_realization.(trait_ctx_spec) Clone_E_lfts_inst Clone_E_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf E_rt E_st E_ty))
  ∗ (Clone_E_realization.(trait_ctx_wf) Clone_E_lfts_inst Clone_E_tys_inst π))%I)) -∗
  Clone_T_clone_loc ◁ᵥ{π, MetaNone} Clone_T_clone_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (Clone_T_lfts_inst : prod_vec lft Clone_T_realization.(trait_ctx_lfts)) (Clone_T_tys_inst : plist type Clone_T_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre ((Clone_clone_spec (RRGS:=RRGS) (Clone_T_realization.(trait_ctx_spec) Clone_T_lfts_inst Clone_T_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (Clone_T_realization.(trait_ctx_wf) Clone_T_lfts_inst Clone_T_tys_inst π))%I)) -∗
  typed_function π (ResultTEasstd_clone_Clone_clone_def Clone_E_clone_loc  Clone_T_clone_loc  T_st  E_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), fn_spec_add_late_pre (type_of_ResultTEasstd_clone_Clone_clone T_rt E_rt T_st E_st Clone_T_spec_attrs Clone_E_spec_attrs DropGlue_T_spec_attrs DropGlue_E_spec_attrs -[ulft_1] -[T_ty; E_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf E_rt E_st E_ty))
  ∗ (((trait_incl_of_ResultTEasstd_clone_Clone_clone (T_rt) (E_rt) (T_st) (E_st) (Clone_T_spec_attrs) (Clone_T_realization) (Clone_E_spec_attrs) (Clone_E_realization) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (DropGlue_E_spec_attrs) (DropGlue_E_realization))-[ulft_1] -[T_ty; E_ty]) π))).
End proof.

Ltac ResultTEasstd_clone_Clone_clone_prelude :=
  unfold ResultTEasstd_clone_Clone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "ResultTEasstd_clone_Clone_clone");
  intros T_rt E_rt T_st E_st Clone_T_spec_attrs Clone_T_realization Clone_E_spec_attrs Clone_E_realization DropGlue_T_spec_attrs DropGlue_T_realization DropGlue_E_spec_attrs DropGlue_E_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  let E_ty := fresh "E_ty" in
  start_function "ResultTEasstd_clone_Clone_clone" ϝ fid ( [ulft_1 [] ] ) ( [T_ty [E_ty [] ] ] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "E" :=
  existT _ (E_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
