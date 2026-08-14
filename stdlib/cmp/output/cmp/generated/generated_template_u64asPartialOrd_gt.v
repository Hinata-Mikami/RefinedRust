From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u64asPartialOrd_gt_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (u64asPartialOrd_gt_def ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u64asPartialOrd_gt -[ulft_1; ulft_2] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_u64asPartialOrd_gt-[ulft_1; ulft_2] -[])%Z⌝))).
End proof.

Ltac u64asPartialOrd_gt_prelude :=
  unfold u64asPartialOrd_gt_lemma;
  set (FN_NAME := FUNCTION_NAME "u64asPartialOrd_gt");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  start_function "u64asPartialOrd_gt" ϝ fid ( [ulft_1 [ulft_2 [] ] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("ulft_2", ulft_2) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
