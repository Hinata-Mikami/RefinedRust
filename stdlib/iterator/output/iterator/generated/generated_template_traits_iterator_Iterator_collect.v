From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step step_by.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition traits_iterator_Iterator_collect_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(B_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(B_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs : !(traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) `(traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (traits_iterator_FromIterator_spec (RRGS:=RRGS) (B_rt) (Item_rt)))) `(DropGlue_B_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt)))) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_from_iter_Self_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (B_st) →
  traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_from_iter_Self_loc ◁ᵥ{π, MetaNone} traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_from_iter_Self_loc @ function_ptr [Self_st] (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Self_ty]) : ([Self_rt; Self_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_FromIterator_from_iter_spec (RRGS:=RRGS) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec-[] -[])) ((Self_rt)) ((Self_rt)) (Self_st) (Self_st) traits_iterator_Iterator_Self_spec_attrs (Iastraits_iterator_IntoIterator_spec_attrs ((Self_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs)) -[] -[Self_ty; Self_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Self_rt Self_st Self_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_collect_def traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_from_iter_Self_loc  Self_st  Item_st  B_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty]) : ([Self_rt; Item_rt; B_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_collect_base_spec Self_rt Item_rt B_rt Self_st Item_st B_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs -[] -[Self_ty; Item_ty; B_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_collect (Self_rt) (Item_rt) (B_rt) (Self_st) (Item_st) (B_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (DropGlue_Self_spec) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec) (DropGlue_B_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec))-[] -[Self_ty; Item_ty; B_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_collect_prelude :=
  unfold traits_iterator_Iterator_collect_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_collect");
  intros Self_rt Item_rt B_rt Self_st Item_st B_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec DropGlue_Self_spec traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec DropGlue_B_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let B_ty := fresh "B_ty" in
  let p := fresh "p" in
  let self := fresh "self" in
  start_function "traits_iterator_Iterator_collect" ϝ fid ( [] ) ( [Self_ty [Item_ty [B_ty [] ] ] ] ) ( [  p self ] ) ( p self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "Item" :=
  existT _ (Item_ty)
      ]>%E $ <[
      "B" :=
  existT _ (B_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
