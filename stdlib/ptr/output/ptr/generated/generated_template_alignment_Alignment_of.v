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
Definition alignment_Alignment_of_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) (Option_T_unwrap_alignment_Alignment_loc : loc) (alignment_Alignment_new_loc : loc) (mem_align_of_T_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  syn_type_is_layoutable (((Option_els (alignment_Alignment_st)) : syn_type)) →
  Option_T_unwrap_alignment_Alignment_loc ◁ᵥ{π, MetaNone} Option_T_unwrap_alignment_Alignment_loc @ function_ptr [((Option_els (alignment_Alignment_st)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Option_T_unwrap (RRGS:=RRGS) ((alignment_Alignment_inv_t_rt)) (alignment_Alignment_st)  <TY> (alignment_Alignment_inv_t    <INST!>) <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_Option_T_unwrap ((alignment_Alignment_inv_t_rt)) (alignment_Alignment_st)  <TY> (alignment_Alignment_inv_t    <INST!>) <INST!>)%Z⌝))%I) -∗
  alignment_Alignment_new_loc ◁ᵥ{π, MetaNone} alignment_Alignment_new_loc @ function_ptr [(IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignment_new (RRGS:=RRGS)   <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_alignment_Alignment_new   <INST!>)%Z⌝))%I) -∗
  mem_align_of_T_loc ◁ᵥ{π, MetaNone} mem_align_of_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mem_align_of (RRGS:=RRGS) ((T_rt)) (T_st)  <TY> T_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜(trait_incl_of_mem_align_of ((T_rt)) (T_st)  <TY> T_ty <INST!>)%Z⌝))%I) -∗
  typed_function π (alignment_Alignment_of_def Option_T_unwrap_alignment_Alignment_loc  alignment_Alignment_new_loc  mem_align_of_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_alignment_Alignment_of T_rt T_st  <TY> T_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_alignment_Alignment_of (T_rt) (T_st)) <TY> T_ty <INST!>)%Z⌝))).
End proof.

Ltac alignment_Alignment_of_prelude :=
  unfold alignment_Alignment_of_lemma;
  set (FN_NAME := FUNCTION_NAME "alignment_Alignment_of");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  start_function "alignment_Alignment_of" ϝ ( [] ) ( [T_ty [] ] ) ( ? ) (  );
  intros;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
