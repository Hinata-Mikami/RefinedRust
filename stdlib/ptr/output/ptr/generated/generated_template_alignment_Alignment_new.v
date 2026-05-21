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
Definition alignment_Alignment_new_lemma (π : thread_id) : Prop :=
  ∀ (alignment_Alignment_new_unchecked_loc : loc) (usize_is_power_of_two_loc : loc) , 
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  syn_type_is_layoutable (((Option_els (alignment_Alignment_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (alignment_Alignment_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (alignment_Alignment_st)) : syn_type)) →
  alignment_Alignment_new_unchecked_loc ◁ᵥ{π, MetaNone} alignment_Alignment_new_unchecked_loc @ function_ptr [(IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignment_new_unchecked (RRGS:=RRGS)  -[] -[]) (λ π, (True))%I) -∗
  usize_is_power_of_two_loc ◁ᵥ{π, MetaNone} usize_is_power_of_two_loc @ function_ptr [(IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usize_is_power_of_two (RRGS:=RRGS)  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (alignment_Alignment_new_def alignment_Alignment_new_unchecked_loc  usize_is_power_of_two_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignment_new -[] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_alignment_Alignment_new-[] -[])%Z⌝))).
End proof.

Ltac alignment_Alignment_new_prelude :=
  unfold alignment_Alignment_new_lemma;
  set (FN_NAME := FUNCTION_NAME "alignment_Alignment_new");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let align := fresh "align" in
  start_function "alignment_Alignment_new" ϝ ( [] ) ( [] ) (  align ) ( align );
  intros arg_align;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
