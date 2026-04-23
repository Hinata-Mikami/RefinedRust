From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.theories Require Export layout shims.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.alloc.alloc Require Export generated_code_alloc generated_specs_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition layout_Layout_from_size_align_lemma (π : thread_id) : Prop :=
  ∀ (layout_Layout_from_size_align_unchecked_loc : loc) , 
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((layout_LayoutError_sls : syn_type)) →
  syn_type_is_layoutable (((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) →
  layout_Layout_from_size_align_unchecked_loc ◁ᵥ{π, MetaNone} layout_Layout_from_size_align_unchecked_loc @ function_ptr [(IntSynType USize); (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_from_size_align_unchecked (RRGS:=RRGS)   <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_layout_Layout_from_size_align_unchecked   <INST!>)%Z⌝))%I) -∗
  typed_function π (layout_Layout_from_size_align_def layout_Layout_from_size_align_unchecked_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_from_size_align  <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_layout_Layout_from_size_align <INST!>)%Z⌝))).
End proof.

Ltac layout_Layout_from_size_align_prelude :=
  unfold layout_Layout_from_size_align_lemma;
  set (FN_NAME := FUNCTION_NAME "layout_Layout_from_size_align");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let size := fresh "size" in
  let align := fresh "align" in
  start_function "layout_Layout_from_size_align" ϝ ( [] ) ( [] ) ( [  size align ] ) (  size align );
  intros arg_size arg_align;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
