From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition adapters_skip_SkipMIastraits_iterator_Iterator_next_lemma (π : thread_id) : Prop :=
  ∀ `(MI_rt : !RT) `(traits_iterator_Iterator_MI_Item_rt : !RT) `(MI_st : !syn_type) `(traits_iterator_Iterator_MI_Item_st : !syn_type) `(traits_iterator_Iterator_MI_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) `(traits_iterator_Iterator_MI_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt)))) (traits_iterator_Iterator_MI_next_loc : loc) (traits_iterator_Iterator_MI_nth_loc : loc) , 
  syn_type_is_layoutable (MI_st) →
  syn_type_is_layoutable (((adapters_skip_Skip_sls (MI_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) →
  traits_iterator_Iterator_MI_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_MI_next_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_MI_spec <INST!>))   <LFT> late_lft_0 <INST!>) (λ π, (True))%I) -∗
  traits_iterator_Iterator_MI_nth_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_MI_nth_loc @ function_ptr [PtrSynType; (IntSynType USize)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_nth_spec (RRGS:=RRGS) (traits_iterator_Iterator_MI_spec <INST!>))   <LFT> late_lft_0 <INST!>) (λ π, (True))%I) -∗
  typed_function π (adapters_skip_SkipMIastraits_iterator_Iterator_next_def traits_iterator_Iterator_MI_next_loc  traits_iterator_Iterator_MI_nth_loc  MI_st  traits_iterator_Iterator_MI_Item_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_skip_SkipMIastraits_iterator_Iterator_next MI_rt traits_iterator_Iterator_MI_Item_rt MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs  <TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <LFT> ulft_1 <INST!>) (λ π, ((typaram_wf MI_rt MI_st MI_ty)
  ∗ (typaram_wf traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_Item_ty))
  ∗ (⌜((trait_incl_of_adapters_skip_SkipMIastraits_iterator_Iterator_next (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (MI_st) (traits_iterator_Iterator_MI_Item_st) (traits_iterator_Iterator_MI_spec_attrs) (traits_iterator_Iterator_MI_spec)) <TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <LFT> ulft_1 <INST!>)%Z⌝))).
End proof.

Ltac adapters_skip_SkipMIastraits_iterator_Iterator_next_prelude :=
  unfold adapters_skip_SkipMIastraits_iterator_Iterator_next_lemma;
  set (FN_NAME := FUNCTION_NAME "adapters_skip_SkipMIastraits_iterator_Iterator_next");
  intros MI_rt traits_iterator_Iterator_MI_Item_rt MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs traits_iterator_Iterator_MI_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let MI_ty := fresh "MI_ty" in
  let traits_iterator_Iterator_MI_Item_ty := fresh "traits_iterator_Iterator_MI_Item_ty" in
  start_function "adapters_skip_SkipMIastraits_iterator_Iterator_next" ϝ ( [ulft_1 [] ] ) ( [MI_ty [traits_iterator_Iterator_MI_Item_ty [] ] ] ) ( ? ) (  );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "MI" :=
  existT _ (MI_ty)
      ]>%E $ <[
      "traits_iterator_Iterator_MI_Item" :=
  existT _ (traits_iterator_Iterator_MI_Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
