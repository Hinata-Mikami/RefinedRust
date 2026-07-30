From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range Require Export generated_code_range generated_specs_range.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition drop_glue_Range_lemma (π : thread_id) : Prop :=
  ∀ `(Idx_rt : !RT) `(Idx_st : !syn_type) `(DropGlue_Idx_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Idx_rt)))) (DropGlue_Idx_drop_glue_loc : loc) , 
  syn_type_is_layoutable (Idx_st) →
  syn_type_is_layoutable (((Range_sls (Idx_st)) : syn_type)) →
  DropGlue_Idx_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_Idx_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_Idx_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (drop_glue_Range_def DropGlue_Idx_drop_glue_loc  Idx_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_Range Idx_rt Idx_st -[] -[Idx_ty]) (λ π, ((typaram_wf Idx_rt Idx_st Idx_ty))
  ∗ (⌜((trait_incl_of_drop_glue_Range (Idx_rt) (Idx_st) (DropGlue_Idx_spec))-[] -[Idx_ty])%Z⌝))).
End proof.

Ltac drop_glue_Range_prelude :=
  unfold drop_glue_Range_lemma;
  set (FN_NAME := FUNCTION_NAME "drop_glue_Range");
  intros Idx_rt Idx_st DropGlue_Idx_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Idx_ty := fresh "Idx_ty" in
  start_function "drop_glue_Range" ϝ ( [] ) ( [Idx_ty [] ] ) ( ? );
  intros arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Idx" :=
  existT _ (Idx_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
