From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition usize_abs_diff_lemma (π : thread_id) : Prop :=
  ∀ (panic_shim_loc : loc) , 
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (usize_abs_diff_def panic_shim_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usize_abs_diff -[] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_usize_abs_diff-[] -[])%Z⌝))).
End proof.

Ltac usize_abs_diff_prelude :=
  unfold usize_abs_diff_lemma;
  set (FN_NAME := FUNCTION_NAME "usize_abs_diff");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let x := fresh "x" in
  let other := fresh "other" in
  start_function "usize_abs_diff" ϝ ( [] ) ( [] ) ( [  x other ] ) ( x other );
  intros arg_x arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
