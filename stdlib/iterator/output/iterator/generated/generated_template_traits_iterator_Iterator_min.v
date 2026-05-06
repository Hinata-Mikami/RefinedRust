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
Definition traits_iterator_Iterator_min_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Item_rt) (Item_rt)))) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Eq_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Item_rt)))) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Item_rt) (Item_rt)))) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Item_rt)))) (traits_iterator_Iterator_Self_min_by_closuresrctraitsiteratorrs2651326519_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  traits_iterator_Iterator_Self_min_by_closuresrctraitsiteratorrs2651326519_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_min_by_closuresrctraitsiteratorrs2651326519_loc @ function_ptr [Self_st; UnitSynType] (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_min_by_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec <INST!>)) (unit) (UnitSynType) (traits_iterator_Iterator_min_closure0_FnOnce_spec_attrs ((Self_rt)) ((Item_rt)) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_min_closure0_FnMut_spec_attrs ((Self_rt)) ((Item_rt)) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))  <TY> unit_t <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_min_def traits_iterator_Iterator_Self_min_by_closuresrctraitsiteratorrs2651326519_loc  Self_st  Item_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_min_base_spec Self_rt Item_rt Self_st Item_st traits_iterator_Iterator_Self_spec_attrs PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs  <TY> Self_ty <TY> Item_ty <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_min (Self_rt) (Item_rt) (Self_st) (Item_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec)) <TY> Self_ty <TY> Item_ty <INST!>)%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_min_prelude :=
  unfold traits_iterator_Iterator_min_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_min");
  intros Self_rt Item_rt Self_st Item_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec Eq_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec Ord_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let p := fresh "p" in
  let self := fresh "self" in
  start_function "traits_iterator_Iterator_min" ϝ ( [] ) ( [Self_ty [Item_ty [] ] ] ) ( [  p self ] ) (  p self );
  intros arg_self;
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
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
