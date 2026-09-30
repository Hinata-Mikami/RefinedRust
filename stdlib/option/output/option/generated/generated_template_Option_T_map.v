From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Option_T_map_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(U_rt : !RT) `(F_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(F_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(FnOnce_F_T_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) )) `(FnOnce_F_T_realization : !(trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt))))) `(DropGlue_U_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) `(DropGlue_U_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_F_drop_glue_loc : loc) (FnOnce_F_T_call_once_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (U_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (U_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (U_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (U_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (T_st)) : syn_type)) →
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I)) -∗
  FnOnce_F_T_call_once_loc ◁ᵥ{π, MetaNone} FnOnce_F_T_call_once_loc @ function_ptr [F_st; ((tuple1_sls (T_st)) : syn_type)] (<tag_type> spec_collapse_params _ _ (λ (FnOnce_F_T_lfts_inst : prod_vec lft FnOnce_F_T_realization.(trait_ctx_lfts)) (FnOnce_F_T_tys_inst : plist type FnOnce_F_T_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[T_ty; U_ty; F_ty]) : ([T_rt; U_rt; F_rt] : list RT), fn_spec_add_late_pre ((FnOnce_call_once_spec (RRGS:=RRGS) (FnOnce_F_T_realization.(trait_ctx_spec) FnOnce_F_T_lfts_inst FnOnce_F_T_tys_inst -[] -[]))  -[] -[]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf U_rt U_st U_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (FnOnce_F_T_realization.(trait_ctx_wf) FnOnce_F_T_lfts_inst FnOnce_F_T_tys_inst π))%I)) -∗
  typed_function π (Option_T_map_def DropGlue_F_drop_glue_loc  FnOnce_F_T_call_once_loc  T_st  U_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty; F_ty]) : ([T_rt; U_rt; F_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_map T_rt U_rt F_rt T_st U_st F_st DropGlue_T_spec_attrs FnOnce_F_T_spec_attrs DropGlue_U_spec_attrs DropGlue_F_spec_attrs -[] -[T_ty; U_ty; F_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf U_rt U_st U_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (((trait_incl_of_Option_T_map (T_rt) (U_rt) (F_rt) (T_st) (U_st) (F_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (FnOnce_F_T_spec_attrs) (FnOnce_F_T_realization) (DropGlue_U_spec_attrs) (DropGlue_U_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization))-[] -[T_ty; U_ty; F_ty]) π))).
End proof.

Ltac Option_T_map_prelude :=
  unfold Option_T_map_lemma;
  set (FN_NAME := FUNCTION_NAME "Option_T_map");
  intros T_rt U_rt F_rt T_st U_st F_st DropGlue_T_spec_attrs DropGlue_T_realization FnOnce_F_T_spec_attrs FnOnce_F_T_realization DropGlue_U_spec_attrs DropGlue_U_realization DropGlue_F_spec_attrs DropGlue_F_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let U_ty := fresh "U_ty" in
  let F_ty := fresh "F_ty" in
  let op := fresh "op" in
  let self := fresh "self" in
  let f := fresh "f" in
  start_function "Option_T_map" ϝ fid ( [] ) ( [T_ty [U_ty [F_ty [] ] ] ] ) ( [ [  op self ] f ] ) ( op self f );
  intros arg_self arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "U" :=
  existT _ (U_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
