From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition i16asMulREFai16_mul_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (i16asMulREFai16_mul_def ) (<tag_type> spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i16asMulREFai16_mul -[ulft_a] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_i16asMulREFai16_mul-[ulft_a] -[])%Z⌝))).
End proof.

Ltac i16asMulREFai16_mul_prelude :=
  unfold i16asMulREFai16_mul_lemma;
  set (FN_NAME := FUNCTION_NAME "i16asMulREFai16_mul");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_a := fresh "ulft_a" in
  start_function "i16asMulREFai16_mul" ϝ ( [ulft_a [] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_a" ulft_a $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
