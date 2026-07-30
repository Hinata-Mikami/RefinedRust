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
Definition adapters_take_TakeMIastraits_iterator_Iterator_next_lemma (π : thread_id) : Prop :=
  ∀ `(MI_rt : !RT) `(traits_iterator_Iterator_MI_Item_rt : !RT) `(MI_st : !syn_type) `(traits_iterator_Iterator_MI_Item_st : !syn_type) `(traits_iterator_Iterator_MI_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) `(traits_iterator_Iterator_MI_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt)))) `(DropGlue_MI_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (MI_rt)))) `(DropGlue_MIastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_MI_Item_rt)))) (traits_iterator_Iterator_MI_next_loc : loc) , 
  syn_type_is_layoutable (MI_st) →
  syn_type_is_layoutable (((adapters_take_Take_sls (MI_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (traits_iterator_Iterator_MI_Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  traits_iterator_Iterator_MI_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_MI_next_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_MI_spec-[] -[]))  -[late_lft_0] -[]) (λ π, (True))%I) -∗
  typed_function π (adapters_take_TakeMIastraits_iterator_Iterator_next_def traits_iterator_Iterator_MI_next_loc  MI_st  traits_iterator_Iterator_MI_Item_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_take_TakeMIastraits_iterator_Iterator_next MI_rt traits_iterator_Iterator_MI_Item_rt MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs -[ulft_1] -[MI_ty; traits_iterator_Iterator_MI_Item_ty]) (λ π, ((typaram_wf MI_rt MI_st MI_ty)
  ∗ (typaram_wf traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_Item_ty))
  ∗ (⌜((trait_incl_of_adapters_take_TakeMIastraits_iterator_Iterator_next (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (MI_st) (traits_iterator_Iterator_MI_Item_st) (traits_iterator_Iterator_MI_spec_attrs) (traits_iterator_Iterator_MI_spec) (DropGlue_MI_spec) (DropGlue_MIastraits_iterator_Iterator_Item_spec))-[ulft_1] -[MI_ty; traits_iterator_Iterator_MI_Item_ty])%Z⌝))).
End proof.

Ltac adapters_take_TakeMIastraits_iterator_Iterator_next_prelude :=
  unfold adapters_take_TakeMIastraits_iterator_Iterator_next_lemma;
  set (FN_NAME := FUNCTION_NAME "adapters_take_TakeMIastraits_iterator_Iterator_next");
  intros MI_rt traits_iterator_Iterator_MI_Item_rt MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs traits_iterator_Iterator_MI_spec DropGlue_MI_spec DropGlue_MIastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let MI_ty := fresh "MI_ty" in
  let traits_iterator_Iterator_MI_Item_ty := fresh "traits_iterator_Iterator_MI_Item_ty" in
  start_function "adapters_take_TakeMIastraits_iterator_Iterator_next" ϝ ( [ulft_1 [] ] ) ( [MI_ty [traits_iterator_Iterator_MI_Item_ty [] ] ] ) ( ? );
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
