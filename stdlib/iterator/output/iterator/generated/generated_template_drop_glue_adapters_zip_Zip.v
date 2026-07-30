From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition drop_glue_adapters_zip_Zip_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(DropGlue_A_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) `(DropGlue_B_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (DropGlue_A_drop_glue_loc : loc) (DropGlue_B_drop_glue_loc : loc) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (B_st) →
  syn_type_is_layoutable (((adapters_zip_Zip_sls (A_st) (B_st)) : syn_type)) →
  DropGlue_A_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_A_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_A_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  DropGlue_B_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_B_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_B_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (drop_glue_adapters_zip_Zip_def DropGlue_A_drop_glue_loc  DropGlue_B_drop_glue_loc  A_st  B_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_adapters_zip_Zip A_rt B_rt A_st B_st -[] -[A_ty; B_ty]) (λ π, ((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (⌜((trait_incl_of_drop_glue_adapters_zip_Zip (A_rt) (B_rt) (A_st) (B_st) (DropGlue_A_spec) (DropGlue_B_spec))-[] -[A_ty; B_ty])%Z⌝))).
End proof.

Ltac drop_glue_adapters_zip_Zip_prelude :=
  unfold drop_glue_adapters_zip_Zip_lemma;
  set (FN_NAME := FUNCTION_NAME "drop_glue_adapters_zip_Zip");
  intros A_rt B_rt A_st B_st DropGlue_A_spec DropGlue_B_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let A_ty := fresh "A_ty" in
  let B_ty := fresh "B_ty" in
  start_function "drop_glue_adapters_zip_Zip" ϝ ( [] ) ( [A_ty [B_ty [] ] ] ) ( ? );
  intros arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ <[
      "B" :=
  existT _ (B_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
