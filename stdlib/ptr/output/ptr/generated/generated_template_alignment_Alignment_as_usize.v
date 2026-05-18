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
Definition alignment_Alignment_as_usize_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  syn_type_is_layoutable ((alignment_AlignmentEnum_els : syn_type)) →
  ⊢ typed_function π (alignment_Alignment_as_usize_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignment_as_usize -[] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_alignment_Alignment_as_usize-[] -[])%Z⌝))).
End proof.

Ltac alignment_Alignment_as_usize_prelude :=
  unfold alignment_Alignment_as_usize_lemma;
  set (FN_NAME := FUNCTION_NAME "alignment_Alignment_as_usize");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let self := fresh "self" in
  start_function "alignment_Alignment_as_usize" ϝ ( [] ) ( [] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
