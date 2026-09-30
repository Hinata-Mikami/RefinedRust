From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition min_by_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(F_rt : !RT) `(T_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_REFTREFT_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt) )) `(FnOnce_F_REFTREFT_realization : !(trait_spec_realization (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (T_rt))) ((place_rfnRT (T_rt))))) (Ordering_rt))))) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_T_drop_glue_loc : loc) (FnOnce_F_REFTREFT_call_once_loc : loc) (Ordering_is_lt_loc : loc) (Ordering_is_lt_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) →
  DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I)) -∗
  FnOnce_F_REFTREFT_call_once_loc ◁ᵥ{π, MetaNone} FnOnce_F_REFTREFT_call_once_loc @ function_ptr [F_st; ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)] (<tag_type> spec_collapse_params _ _ (λ (FnOnce_F_REFTREFT_lfts_inst : prod_vec lft FnOnce_F_REFTREFT_realization.(trait_ctx_lfts)) (FnOnce_F_REFTREFT_tys_inst : plist type FnOnce_F_REFTREFT_realization.(trait_ctx_tys)), spec! ( *[_lft_for_1; _lft_for_0; vlft6; vlft7]) : 4 | ( *[T_ty; F_ty]) : ([T_rt; F_rt] : list RT), fn_spec_add_late_pre ((FnOnce_call_once_spec (RRGS:=RRGS) (FnOnce_F_REFTREFT_realization.(trait_ctx_spec) FnOnce_F_REFTREFT_lfts_inst FnOnce_F_REFTREFT_tys_inst -[_lft_for_1; _lft_for_0] -[]))  -[] -[]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (FnOnce_F_REFTREFT_realization.(trait_ctx_wf) FnOnce_F_REFTREFT_lfts_inst FnOnce_F_REFTREFT_tys_inst π))%I)) -∗
  Ordering_is_lt_loc ◁ᵥ{π, MetaNone} Ordering_is_lt_loc @ function_ptr [Ordering_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Ordering_is_lt (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (Ordering_is_lt_loc_linking -[] -[] π)))%I) -∗
  typed_function π (min_by_def DropGlue_T_drop_glue_loc  FnOnce_F_REFTREFT_call_once_loc  Ordering_is_lt_loc  T_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; F_ty]) : ([T_rt; F_rt] : list RT), fn_spec_add_late_pre (type_of_min_by T_rt F_rt T_st F_st FnOnce_F_REFTREFT_spec_attrs DropGlue_T_spec_attrs DropGlue_F_spec_attrs -[] -[T_ty; F_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (((trait_incl_of_min_by (T_rt) (F_rt) (T_st) (F_st) (FnOnce_F_REFTREFT_spec_attrs) (FnOnce_F_REFTREFT_realization) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization))-[] -[T_ty; F_ty]) π)
  ∗ (□ (Ordering_is_lt_loc_linking -[] -[] π)))).
End proof.

Ltac min_by_prelude :=
  unfold min_by_lemma;
  set (FN_NAME := FUNCTION_NAME "min_by");
  intros T_rt F_rt T_st F_st FnOnce_F_REFTREFT_spec_attrs FnOnce_F_REFTREFT_realization DropGlue_T_spec_attrs DropGlue_T_realization DropGlue_F_spec_attrs DropGlue_F_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  let compare := fresh "compare" in
  start_function "min_by" ϝ fid ( [] ) ( [T_ty [F_ty [] ] ] ) ( [ [ [  p v1 ] v2 ] compare ] ) ( p v1 v2 compare );
  intros arg_v1 arg_v2 arg_compare;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
