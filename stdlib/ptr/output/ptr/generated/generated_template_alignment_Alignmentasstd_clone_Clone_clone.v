From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.theories Require Export alignment shims specs.
From rrstd.ptr.ptr Require Export generated_code_ptr generated_specs_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition alignment_Alignmentasstd_clone_Clone_clone_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  ⊢ typed_function π (alignment_Alignmentasstd_clone_Clone_clone_def ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignmentasstd_clone_Clone_clone -[ulft_1] -[]) (λ π, (True)
  ∗ ((trait_incl_of_alignment_Alignmentasstd_clone_Clone_clone-[ulft_1] -[]) π))).
End proof.

Ltac alignment_Alignmentasstd_clone_Clone_clone_prelude :=
  unfold alignment_Alignmentasstd_clone_Clone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "alignment_Alignmentasstd_clone_Clone_clone");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  start_function "alignment_Alignmentasstd_clone_Clone_clone" ϝ fid ( [ulft_1 [] ] ) ( [] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
