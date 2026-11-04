From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.clone.clone Require Export generated_code_clone generated_specs_clone.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition i128asClone_clone_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (i128asClone_clone_def ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i128asClone_clone -[ulft_1] -[]) (λ π, (True)
  ∗ ((trait_incl_of_i128asClone_clone-[ulft_1] -[]) π))).
End proof.

Ltac i128asClone_clone_prelude :=
  unfold i128asClone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "i128asClone_clone");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  start_function "i128asClone_clone" ϝ fid ( [ulft_1 [] ] ) ( [] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
