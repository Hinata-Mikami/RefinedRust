From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Option_T_ok_or_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_E_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (E_rt) )) `(DropGlue_E_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt))))) (DropGlue_E_drop_glue_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (E_st) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_els (T_st) (E_st)) : syn_type)) →
  DropGlue_E_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_E_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_E_lfts_inst : prod_vec lft DropGlue_E_realization.(trait_ctx_lfts)) (DropGlue_E_tys_inst : plist type DropGlue_E_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_E_realization.(trait_ctx_spec) DropGlue_E_lfts_inst DropGlue_E_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_E_realization.(trait_ctx_wf) DropGlue_E_lfts_inst DropGlue_E_tys_inst π))%I)) -∗
  typed_function π (Option_T_ok_or_def DropGlue_E_drop_glue_loc  T_st  E_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_ok_or T_rt E_rt T_st E_st DropGlue_T_spec_attrs DropGlue_E_spec_attrs -[] -[T_ty; E_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf E_rt E_st E_ty))
  ∗ (((trait_incl_of_Option_T_ok_or (T_rt) (E_rt) (T_st) (E_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (DropGlue_E_spec_attrs) (DropGlue_E_realization))-[] -[T_ty; E_ty]) π))).
End proof.

Ltac Option_T_ok_or_prelude :=
  unfold Option_T_ok_or_lemma;
  set (FN_NAME := FUNCTION_NAME "Option_T_ok_or");
  intros T_rt E_rt T_st E_st DropGlue_T_spec_attrs DropGlue_T_realization DropGlue_E_spec_attrs DropGlue_E_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let E_ty := fresh "E_ty" in
  let self := fresh "self" in
  let err := fresh "err" in
  start_function "Option_T_ok_or" ϝ fid ( [] ) ( [T_ty [E_ty [] ] ] ) ( [  self err ] ) ( self err );
  intros arg_self arg_err;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "E" :=
  existT _ (E_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
