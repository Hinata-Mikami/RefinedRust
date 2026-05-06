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
Definition traits_iterator_Iterator_position_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) (ControlFlow_BC_break_value_usize_unit_loc : loc) (traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1811318119_std_ops_ControlFlowusize_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable ((convert_Infallible_els : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els ((IntSynType USize)) ((convert_Infallible_els : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_els ((IntSynType USize))) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) →
  ControlFlow_BC_break_value_usize_unit_loc ◁ᵥ{π, MetaNone} ControlFlow_BC_break_value_usize_unit_loc @ function_ptr [((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_ControlFlow_BC_break_value (RRGS:=RRGS) (Z) (unit) ((IntSynType USize)) (UnitSynType)  <TY> (int USize) <TY> unit_t <INST!>) (λ π, (True))%I) -∗
  traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1811318119_std_ops_ControlFlowusize_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1811318119_std_ops_ControlFlowusize_loc @ function_ptr [PtrSynType; UnitSynType; ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)] (<tag_type> spec! ( *[vlft8; vlft9; late_lft_0]) : 3 | ( *[Self_ty; F_ty; Item_ty]) : ([Self_rt; F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_try_fold_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec <INST!>)) (unit) ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) (((((ControlFlow_rt)) (Z) (unit)))) (((((ControlFlow_rt)) (Z) ((((convert_Infallible_rt))))))) (UnitSynType) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) (((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) (((ControlFlow_els ((IntSynType USize)) ((convert_Infallible_els : syn_type))) : syn_type)) (traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) (ControlFlowBCasFromResidualControlFlowBconvert_Infallible_spec_attrs (Z) (unit)) (traits_iterator_Iterator_position_closure0_FnMut_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) (ControlFlowBCasTry_spec_attrs (Z) (unit))  <TY> unit_t <TY> (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)  <TY> (mut_ref vlft8 F_ty) <TY> (mut_ref vlft9 (int USize)) <INST!>) <TY> (ControlFlow_ty (Z) (unit)  <TY> (int USize) <TY> unit_t <INST!>) <TY> (ControlFlow_ty (Z) ((((convert_Infallible_rt))))  <TY> (int USize) <TY> (convert_Infallible_ty   <INST!>) <INST!>) <LFT> late_lft_0 <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_position_def ControlFlow_BC_break_value_usize_unit_loc  traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1811318119_std_ops_ControlFlowusize_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_position_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs  <TY> Self_ty <TY> Item_ty <TY> F_ty <LFT> ulft_1 <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_position (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec)) <TY> Self_ty <TY> Item_ty <TY> F_ty <LFT> ulft_1 <INST!>)%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_position_prelude :=
  unfold traits_iterator_Iterator_position_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_position");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let P := fresh "P" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_position" ϝ ( [ulft_1 [] ] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [ [  p P ] ClosInv ] self ] f ] ) (  p P ClosInv self f );
  intros arg_self arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
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
