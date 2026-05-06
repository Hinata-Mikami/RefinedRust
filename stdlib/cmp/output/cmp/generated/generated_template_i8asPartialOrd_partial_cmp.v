From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition i8asPartialOrd_partial_cmp_lemma (π : thread_id) : Prop :=
  ∀ (i8asOrd_cmp_loc : loc) , 
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  syn_type_is_layoutable (((Option_els (Ordering_st)) : syn_type)) →
  i8asOrd_cmp_loc ◁ᵥ{π, MetaNone} i8asOrd_cmp_loc @ function_ptr [PtrSynType; PtrSynType] (<tag_type> spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i8asOrd_cmp (RRGS:=RRGS)   <LFT> late_lft_0 <LFT> late_lft_1 <INST!>) (λ π, (True))%I) -∗
  typed_function π (i8asPartialOrd_partial_cmp_def i8asOrd_cmp_loc  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i8asPartialOrd_partial_cmp  <LFT> ulft_1 <LFT> ulft_2 <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_i8asPartialOrd_partial_cmp <LFT> ulft_1 <LFT> ulft_2 <INST!>)%Z⌝))).
End proof.

Ltac i8asPartialOrd_partial_cmp_prelude :=
  unfold i8asPartialOrd_partial_cmp_lemma;
  set (FN_NAME := FUNCTION_NAME "i8asPartialOrd_partial_cmp");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  start_function "i8asPartialOrd_partial_cmp" ϝ ( [ulft_1 [ulft_2 [] ] ] ) ( [] ) ( ? ) (  );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
