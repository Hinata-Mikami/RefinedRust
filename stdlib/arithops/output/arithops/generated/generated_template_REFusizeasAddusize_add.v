From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFusizeasAddusize_add_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (REFusizeasAddusize_add_def ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_REFusizeasAddusize_add -[ulft_1] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_REFusizeasAddusize_add-[ulft_1] -[])%Z⌝))).
End proof.

Ltac REFusizeasAddusize_add_prelude :=
  unfold REFusizeasAddusize_add_lemma;
  set (FN_NAME := FUNCTION_NAME "REFusizeasAddusize_add");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  start_function "REFusizeasAddusize_add" ϝ ( [ulft_1 [] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
