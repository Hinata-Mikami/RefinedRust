From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step step_by.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition drop_glue_adapters_skip_Skip_lemma (π : thread_id) : Prop :=
  ∀ `(I_rt : !RT) `(I_st : !syn_type) `(DropGlue_I_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (I_rt) )) `(DropGlue_I_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (I_rt)))) (DropGlue_I_drop_glue_loc : loc) , 
  syn_type_is_layoutable (I_st) →
  syn_type_is_layoutable (((adapters_skip_Skip_sls (I_st)) : syn_type)) →
  DropGlue_I_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_I_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_I_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (drop_glue_adapters_skip_Skip_def DropGlue_I_drop_glue_loc  I_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_adapters_skip_Skip I_rt I_st DropGlue_I_spec_attrs -[] -[I_ty]) (λ π, ((typaram_wf I_rt I_st I_ty))
  ∗ (⌜((trait_incl_of_drop_glue_adapters_skip_Skip (I_rt) (I_st) (DropGlue_I_spec_attrs) (DropGlue_I_spec))-[] -[I_ty])%Z⌝))).
End proof.

Ltac drop_glue_adapters_skip_Skip_prelude :=
  unfold drop_glue_adapters_skip_Skip_lemma;
  set (FN_NAME := FUNCTION_NAME "drop_glue_adapters_skip_Skip");
  intros I_rt I_st DropGlue_I_spec_attrs DropGlue_I_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let I_ty := fresh "I_ty" in
  start_function "drop_glue_adapters_skip_Skip" ϝ fid ( [] ) ( [I_ty [] ] ) ( ? );
  intros arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "I" :=
  existT _ (I_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
