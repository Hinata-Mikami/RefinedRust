From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition i32_is_negative_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (i32_is_negative_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i32_is_negative -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_i32_is_negative-[] -[]) π))).
End proof.

Ltac i32_is_negative_prelude :=
  unfold i32_is_negative_lemma;
  set (FN_NAME := FUNCTION_NAME "i32_is_negative");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let x := fresh "x" in
  start_function "i32_is_negative" ϝ fid ( [] ) ( [] ) (  x ) ( x );
  intros arg_x;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
