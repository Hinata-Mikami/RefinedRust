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
Definition adapters_map_MapMIMFastraits_iterator_Iterator_next_lemma (π : thread_id) : Prop :=
  ∀ `(MB_rt : !RT) `(MI_rt : !RT) `(MF_rt : !RT) `(traits_iterator_Iterator_MI_Item_rt : !RT) `(MB_st : !syn_type) `(MI_st : !syn_type) `(MF_st : !syn_type) `(traits_iterator_Iterator_MI_Item_st : !syn_type) `(traits_iterator_Iterator_MI_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) `(traits_iterator_Iterator_MI_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt)))) `(FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) `(FnOnce_MF_MIastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt)))) `(FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) `(FnMut_MF_MIastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt)))) `(DropGlue_MB_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (MB_rt)))) `(DropGlue_MI_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (MI_rt)))) `(DropGlue_MF_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (MF_rt)))) `(DropGlue_MIastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_MI_Item_rt)))) (Option_T_map_MIastraits_iterator_Iterator_Item_MB_REFmutMF_loc : loc) (traits_iterator_Iterator_MI_next_loc : loc) , 
  syn_type_is_layoutable (MB_st) →
  syn_type_is_layoutable (MI_st) →
  syn_type_is_layoutable (MF_st) →
  syn_type_is_layoutable (((adapters_map_Map_sls (MI_st) (MF_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (MB_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) →
  Option_T_map_MIastraits_iterator_Iterator_Item_MB_REFmutMF_loc ◁ᵥ{π, MetaNone} Option_T_map_MIastraits_iterator_Iterator_Item_MB_REFmutMF_loc @ function_ptr [((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type); RefSynType] (<tag_type> spec! ( *[vlft5]) : 1 | ( *[MB_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_map (RRGS:=RRGS) ((traits_iterator_Iterator_MI_Item_rt)) ((MB_rt)) (((place_rfnRT (MF_rt)) * gname)%type) (traits_iterator_Iterator_MI_Item_st) (MB_st) (RefSynType) (REFmutFasFnOnceA_spec_attrs ((((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt))))) ((MF_rt)) ((MB_rt)) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) -[] -[traits_iterator_Iterator_MI_Item_ty; MB_ty; (mut_ref vlft5 MF_ty)]) (λ π, ((typaram_wf MB_rt MB_st MB_ty)
  ∗ (typaram_wf MF_rt MF_st MF_ty)
  ∗ (typaram_wf traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_Item_ty)))%I) -∗
  traits_iterator_Iterator_MI_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_MI_next_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_MI_spec-[] -[]))  -[late_lft_0] -[]) (λ π, (True))%I) -∗
  typed_function π (adapters_map_MapMIMFastraits_iterator_Iterator_next_def Option_T_map_MIastraits_iterator_Iterator_Item_MB_REFmutMF_loc  traits_iterator_Iterator_MI_next_loc  MB_st  MI_st  MF_st  traits_iterator_Iterator_MI_Item_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MI_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_map_MapMIMFastraits_iterator_Iterator_next MB_rt MI_rt MF_rt traits_iterator_Iterator_MI_Item_rt MB_st MI_st MF_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs -[ulft_1] -[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) (λ π, ((typaram_wf MB_rt MB_st MB_ty)
  ∗ (typaram_wf MI_rt MI_st MI_ty)
  ∗ (typaram_wf MF_rt MF_st MF_ty)
  ∗ (typaram_wf traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_Item_ty))
  ∗ (⌜((trait_incl_of_adapters_map_MapMIMFastraits_iterator_Iterator_next (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (MB_st) (MI_st) (MF_st) (traits_iterator_Iterator_MI_Item_st) (traits_iterator_Iterator_MI_spec_attrs) (traits_iterator_Iterator_MI_spec) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec) (DropGlue_MB_spec) (DropGlue_MI_spec) (DropGlue_MF_spec) (DropGlue_MIastraits_iterator_Iterator_Item_spec))-[ulft_1] -[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty])%Z⌝))).
End proof.

Ltac adapters_map_MapMIMFastraits_iterator_Iterator_next_prelude :=
  unfold adapters_map_MapMIMFastraits_iterator_Iterator_next_lemma;
  set (FN_NAME := FUNCTION_NAME "adapters_map_MapMIMFastraits_iterator_Iterator_next");
  intros MB_rt MI_rt MF_rt traits_iterator_Iterator_MI_Item_rt MB_st MI_st MF_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs traits_iterator_Iterator_MI_spec FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs FnOnce_MF_MIastraits_iterator_Iterator_Item_spec FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs FnMut_MF_MIastraits_iterator_Iterator_Item_spec DropGlue_MB_spec DropGlue_MI_spec DropGlue_MF_spec DropGlue_MIastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let MB_ty := fresh "MB_ty" in
  let MI_ty := fresh "MI_ty" in
  let MF_ty := fresh "MF_ty" in
  let traits_iterator_Iterator_MI_Item_ty := fresh "traits_iterator_Iterator_MI_Item_ty" in
  start_function "adapters_map_MapMIMFastraits_iterator_Iterator_next" ϝ ( [ulft_1 [] ] ) ( [MB_ty [MI_ty [MF_ty [traits_iterator_Iterator_MI_Item_ty [] ] ] ] ] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "MB" :=
  existT _ (MB_ty)
      ]>%E $ <[
      "MI" :=
  existT _ (MI_ty)
      ]>%E $ <[
      "MF" :=
  existT _ (MF_ty)
      ]>%E $ <[
      "traits_iterator_Iterator_MI_Item" :=
  existT _ (traits_iterator_Iterator_MI_Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
