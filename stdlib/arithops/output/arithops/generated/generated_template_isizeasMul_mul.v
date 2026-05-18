From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition isizeasMul_mul_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (isizeasMul_mul_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_isizeasMul_mul -[] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_isizeasMul_mul-[] -[])%Z⌝))).
End proof.

Ltac isizeasMul_mul_prelude :=
  unfold isizeasMul_mul_lemma;
  set (FN_NAME := FUNCTION_NAME "isizeasMul_mul");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  start_function "isizeasMul_mul" ϝ ( [] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
