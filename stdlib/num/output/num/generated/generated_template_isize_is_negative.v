From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition isize_is_negative_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (isize_is_negative_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_isize_is_negative -[] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_isize_is_negative-[] -[])%Z⌝))).
End proof.

Ltac isize_is_negative_prelude :=
  unfold isize_is_negative_lemma;
  set (FN_NAME := FUNCTION_NAME "isize_is_negative");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let x := fresh "x" in
  start_function "isize_is_negative" ϝ ( [] ) ( [] ) (  x ) (  x );
  intros arg_x;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
