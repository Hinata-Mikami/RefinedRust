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
Definition traits_iterator_Iterator_reduce_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt)))) `(FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) `(FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt)))) (std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc : loc) (std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc : loc) (traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc : loc) (traits_iterator_Iterator_Self_next_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable ((convert_Infallible_els : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc ◁ᵥ{π, MetaNone} std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc @ function_ptr [((Option_els ((convert_Infallible_els : syn_type))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[Item_ty]) : ([Item_rt] : list RT), fn_spec_add_late_pre (type_of_std_option_OptionTasFromResidual_from_residual (RRGS:=RRGS) ((Item_rt)) (Item_st)  <TY> Item_ty <INST!>) (λ π, ((typaram_wf Item_rt Item_st Item_ty))
  ∗ (⌜(trait_incl_of_std_option_OptionTasFromResidual_from_residual ((Item_rt)) (Item_st)  <TY> Item_ty <INST!>)%Z⌝))%I) -∗
  std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc ◁ᵥ{π, MetaNone} std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc @ function_ptr [((Option_els (Item_st)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[Item_ty]) : ([Item_rt] : list RT), fn_spec_add_late_pre (type_of_std_option_OptionTasTry_branch (RRGS:=RRGS) ((Item_rt)) (Item_st)  <TY> Item_ty <INST!>) (λ π, ((typaram_wf Item_rt Item_st Item_ty))
  ∗ (⌜(trait_incl_of_std_option_OptionTasTry_branch ((Item_rt)) (Item_st)  <TY> Item_ty <INST!>)%Z⌝))%I) -∗
  traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc @ function_ptr [Self_st; Item_st; F_st] (<tag_type> spec! ( *[]) : 0 | ( *[F_ty; Item_ty]) : ([F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_fold_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec <INST!>)) ((Item_rt)) ((F_rt)) (Item_st) (F_st) FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs  <TY> Item_ty <TY> F_ty <INST!>) (λ π, ((typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (⌜(True)%Z⌝))%I) -∗
  traits_iterator_Iterator_Self_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_next_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec <INST!>))   <LFT> late_lft_0 <INST!>) (λ π, (True)
  ∗ (⌜(True)%Z⌝))%I) -∗
  typed_function π (traits_iterator_Iterator_reduce_def std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc  std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc  traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc  traits_iterator_Iterator_Self_next_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_reduce_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs  <TY> Self_ty <TY> Item_ty <TY> F_ty <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_reduce (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec)) <TY> Self_ty <TY> Item_ty <TY> F_ty <INST!>)%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_reduce_prelude :=
  unfold traits_iterator_Iterator_reduce_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_reduce");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_reduce" ϝ ( [] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [  p ClosInv ] self ] f ] ) (  p ClosInv self f );
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
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
