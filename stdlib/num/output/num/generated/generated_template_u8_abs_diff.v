From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u8_abs_diff_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (u8_abs_diff_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u8_abs_diff -[] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_u8_abs_diff-[] -[])%Z⌝))).
End proof.

Ltac u8_abs_diff_prelude :=
  unfold u8_abs_diff_lemma;
  set (FN_NAME := FUNCTION_NAME "u8_abs_diff");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let x := fresh "x" in
  let other := fresh "other" in
  start_function "u8_abs_diff" ϝ ( [] ) ( [] ) ( [  x other ] ) (  x other );
  intros arg_x arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
