From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map skip step step_by take.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition adapters_step_by_StepBy_I_new_lemma (π : thread_id) : Prop :=
  ∀ `(I_rt : !RT) `(I_st : !syn_type) `(DropGlue_I_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (I_rt) )) `(DropGlue_I_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (I_rt))))) (DropGlue_I_drop_glue_loc : loc) (panic_shim_loc : loc) (panic_shim_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (I_st) →
  syn_type_is_layoutable (((adapters_step_by_StepBy_sls (I_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  DropGlue_I_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_I_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_I_lfts_inst : prod_vec lft DropGlue_I_realization.(trait_ctx_lfts)) (DropGlue_I_tys_inst : plist type DropGlue_I_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_I_realization.(trait_ctx_spec) DropGlue_I_lfts_inst DropGlue_I_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_I_realization.(trait_ctx_wf) DropGlue_I_lfts_inst DropGlue_I_tys_inst π))%I)) -∗
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (panic_shim_loc_linking -[] -[] π)))%I) -∗
  typed_function π (adapters_step_by_StepBy_I_new_def DropGlue_I_drop_glue_loc  panic_shim_loc  I_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_step_by_StepBy_I_new I_rt I_st DropGlue_I_spec_attrs -[] -[I_ty]) (λ π, ((typaram_wf I_rt I_st I_ty))
  ∗ (((trait_incl_of_adapters_step_by_StepBy_I_new (I_rt) (I_st) (DropGlue_I_spec_attrs) (DropGlue_I_realization))-[] -[I_ty]) π)
  ∗ (□ (panic_shim_loc_linking -[] -[] π)))).
End proof.

Ltac adapters_step_by_StepBy_I_new_prelude :=
  unfold adapters_step_by_StepBy_I_new_lemma;
  set (FN_NAME := FUNCTION_NAME "adapters_step_by_StepBy_I_new");
  intros I_rt I_st DropGlue_I_spec_attrs DropGlue_I_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let I_ty := fresh "I_ty" in
  let iter := fresh "iter" in
  let step := fresh "step" in
  start_function "adapters_step_by_StepBy_I_new" ϝ fid ( [] ) ( [I_ty [] ] ) ( [  iter step ] ) ( iter step );
  intros arg_iter arg_step;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "I" :=
  existT _ (I_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
