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
Definition traits_iterator_Iterator_map_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(B_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(B_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt)))) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt)))) (adapters_map_Map_IF_new_Self_F_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (B_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((adapters_map_Map_sls (Self_st) (F_st)) : syn_type)) →
  adapters_map_Map_IF_new_Self_F_loc ◁ᵥ{π, MetaNone} adapters_map_Map_IF_new_Self_F_loc @ function_ptr [Self_st; F_st] (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; F_ty]) : ([Self_rt; F_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_map_Map_IF_new (RRGS:=RRGS) ((Self_rt)) ((F_rt)) (Self_st) (F_st) -[] -[Self_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_map_def adapters_map_Map_IF_new_Self_F_loc  Self_st  Item_st  B_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([Self_rt; Item_rt; B_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_map_base_spec Self_rt Item_rt B_rt F_rt Self_st Item_st B_st F_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs -[] -[Self_ty; Item_ty; B_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_map (Self_rt) (Item_rt) (B_rt) (F_rt) (Self_st) (Item_st) (B_st) (F_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec))-[] -[Self_ty; Item_ty; B_ty; F_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_map_prelude :=
  unfold traits_iterator_Iterator_map_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_map");
  intros Self_rt Item_rt B_rt F_rt Self_st Item_st B_st F_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let B_ty := fresh "B_ty" in
  let F_ty := fresh "F_ty" in
  let p_inner := fresh "p_inner" in
  let Inv := fresh "Inv" in
  let ParamPred := fresh "ParamPred" in
  let self := fresh "self" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_map" ϝ ( [] ) ( [Self_ty [Item_ty [B_ty [F_ty [] ] ] ] ] ) ( [ [ [ [  p_inner Inv ] ParamPred ] self ] f ] ) (  p_inner Inv ParamPred self f );
  intros arg_self arg_f;
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
      "B" :=
  existT _ (B_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
