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
Definition traits_iterator_Iterator_max_by_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt)))) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec : !(spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt)))))) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec : !(spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt)))))) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) (DropGlue_F_drop_glue_loc : loc) (traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2471324719_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (PtrSynType)) : syn_type)) →
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2471324719_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2471324719_loc @ function_ptr [Self_st; ((tuple1_sls (PtrSynType)) : syn_type)] (<tag_type> spec! ( *[vlft4]) : 1 | ( *[Self_ty; F_ty; Item_ty]) : ([Self_rt; F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_reduce_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec-[] -[])) ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) (((tuple1_sls (PtrSynType)) : syn_type)) (traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_max_by_closure0_FnMut_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) -[] -[(tuple1_ty (((place_rfnRT (F_rt)) * gname)%type) -[] -[(mut_ref vlft4 F_ty)])]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_max_by_def DropGlue_F_drop_glue_loc  traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2471324719_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_max_by_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs -[] -[Self_ty; Item_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_max_by (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (DropGlue_Self_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec) (DropGlue_F_spec))-[] -[Self_ty; Item_ty; F_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_max_by_prelude :=
  unfold traits_iterator_Iterator_max_by_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_max_by");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec DropGlue_Self_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec DropGlue_F_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let compare := fresh "compare" in
  start_function "traits_iterator_Iterator_max_by" ϝ ( [] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [  p ClosInv ] self ] compare ] ) ( p ClosInv self compare );
  intros arg_self arg_compare;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "Item" :=
  existT _ (Item_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
