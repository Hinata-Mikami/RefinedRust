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
Definition traits_iterator_Iterator_position_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt)))) (ControlFlow_BC_break_value_usize_unit_loc : loc) (DropGlue_F_drop_glue_loc : loc) (traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1861318619_std_ops_ControlFlowusize_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els ((IntSynType USize)) (NeverSynType)) : syn_type)) →
  syn_type_is_layoutable (((Option_els ((IntSynType USize))) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) →
  ControlFlow_BC_break_value_usize_unit_loc ◁ᵥ{π, MetaNone} ControlFlow_BC_break_value_usize_unit_loc @ function_ptr [((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_ControlFlow_BC_break_value (RRGS:=RRGS) (Z) (unit) ((IntSynType USize)) (UnitSynType) -[] -[(int USize); unit_t]) (λ π, (True))%I) -∗
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1861318619_std_ops_ControlFlowusize_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1861318619_std_ops_ControlFlowusize_loc @ function_ptr [RefSynType; UnitSynType; ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)] (<tag_type> spec! ( *[vlft8; vlft9; late_lft_0]) : 3 | ( *[Self_ty; F_ty; Item_ty]) : ([Self_rt; F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_try_fold_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec-[] -[])) (unit) ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) (((((ControlFlow_rt)) (Z) (unit)))) (((((ControlFlow_rt)) (Z) (unit)))) (UnitSynType) (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) (((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) (((ControlFlow_els ((IntSynType USize)) (NeverSynType)) : syn_type)) (traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) (ControlFlowBCasFromResidualControlFlowB_spec_attrs (Z) (unit)) (traits_iterator_Iterator_position_closure0_FnMut_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) (ControlFlowBCasTry_spec_attrs (Z) (unit)) -[late_lft_0] -[unit_t; (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type) -[] -[(mut_ref vlft8 F_ty); (mut_ref vlft9 (int USize))]); (ControlFlow_ty (Z) (unit) -[] -[(int USize); unit_t]); (ControlFlow_ty (Z) (unit) -[] -[(int USize); never_t])]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_position_def ControlFlow_BC_break_value_usize_unit_loc  DropGlue_F_drop_glue_loc  traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1861318619_std_ops_ControlFlowusize_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_position_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs -[ulft_1] -[Self_ty; Item_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_position (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (DropGlue_Self_spec) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec) (DropGlue_F_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec))-[ulft_1] -[Self_ty; Item_ty; F_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_position_prelude :=
  unfold traits_iterator_Iterator_position_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_position");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec DropGlue_Self_spec FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec DropGlue_F_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let P := fresh "P" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_position" ϝ fid ( [ulft_1 [] ] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [ [  p P ] ClosInv ] self ] f ] ) ( p P ClosInv self f );
  intros arg_self arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
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
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
