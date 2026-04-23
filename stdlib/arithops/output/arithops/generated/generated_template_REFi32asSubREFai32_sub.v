From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFi32asSubREFai32_sub_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (REFi32asSubREFai32_sub_def ) (<tag_type> spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_REFi32asSubREFai32_sub  <LFT> ulft_a <LFT> ulft_2 <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_REFi32asSubREFai32_sub <LFT> ulft_a <LFT> ulft_2 <INST!>)%Z⌝))).
End proof.

Ltac REFi32asSubREFai32_sub_prelude :=
  unfold REFi32asSubREFai32_sub_lemma;
  set (FN_NAME := FUNCTION_NAME "REFi32asSubREFai32_sub");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_a := fresh "ulft_a" in
  let ulft_2 := fresh "ulft_2" in
  start_function "REFi32asSubREFai32_sub" ϝ ( [ulft_a [ulft_2 [] ] ] ) ( [] ) ( ? ) (  );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_a" ulft_a $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
