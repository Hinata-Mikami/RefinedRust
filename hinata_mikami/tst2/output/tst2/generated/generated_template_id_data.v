From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst2 Require Import generated_code_tst2 generated_specs_tst2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition id_data_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable ((Data_sls : syn_type)) →
  ⊢ typed_function π (id_data_def ) [Data_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_id_data  <INST!>) (λ π, True ∗ ⌜trait_incl_of_id_data <INST!>⌝)).
End proof.

Ltac id_data_prelude :=
  unfold id_data_lemma;
  set (FN_NAME := FUNCTION_NAME "id_data");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let d := fresh "d" in
  start_function "id_data" ϝ ( [] ) ( [] ) (  d ) (  d );
  intros arg_d local___0;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
