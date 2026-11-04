From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.theories Require Export layout shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.alloc.alloc Require Export generated_code_alloc generated_specs_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition alloc_dealloc_internal_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (alloc_dealloc_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alloc_dealloc_internal -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_alloc_dealloc_internal-[] -[]) π))).
End proof.

Ltac alloc_dealloc_internal_prelude :=
  unfold alloc_dealloc_internal_lemma;
  set (FN_NAME := FUNCTION_NAME "alloc_dealloc_internal");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let size := fresh "size" in
  let align_log2 := fresh "align_log2" in
  let ptr := fresh "ptr" in
  start_function "alloc_dealloc_internal" ϝ fid ( [] ) ( [] ) ( [ [  size align_log2 ] ptr ] ) ( size align_log2 ptr );
  intros arg_size arg_align_log2 arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
