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
Definition layout_Layout_align_lemma (π : thread_id) : Prop :=
  ∀ (alignment_Alignment_as_usize_loc : loc) (alignment_Alignment_as_usize_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  alignment_Alignment_as_usize_loc ◁ᵥ{π, MetaNone} alignment_Alignment_as_usize_loc @ function_ptr [(alignment_Alignment_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignment_as_usize (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (alignment_Alignment_as_usize_loc_linking -[] -[] π)))%I) -∗
  typed_function π (layout_Layout_align_def alignment_Alignment_as_usize_loc  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_align -[ulft_1] -[]) (λ π, (True)
  ∗ ((trait_incl_of_layout_Layout_align-[ulft_1] -[]) π)
  ∗ (□ (alignment_Alignment_as_usize_loc_linking -[] -[] π)))).
End proof.

Ltac layout_Layout_align_prelude :=
  unfold layout_Layout_align_lemma;
  set (FN_NAME := FUNCTION_NAME "layout_Layout_align");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let self := fresh "self" in
  start_function "layout_Layout_align" ϝ fid ( [ulft_1 [] ] ) ( [] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
