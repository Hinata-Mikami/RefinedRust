From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u128asAdd_add_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (u128asAdd_add_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u128asAdd_add  <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_u128asAdd_add <INST!>)%Z⌝))).
End proof.

Ltac u128asAdd_add_prelude :=
  unfold u128asAdd_add_lemma;
  set (FN_NAME := FUNCTION_NAME "u128asAdd_add");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  start_function "u128asAdd_add" ϝ ( [] ) ( [] ) ( ? ) (  );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
