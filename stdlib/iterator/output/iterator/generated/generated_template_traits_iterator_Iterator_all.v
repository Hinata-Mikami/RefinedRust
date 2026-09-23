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
Definition traits_iterator_Iterator_all_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt)))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) (DropGlue_F_drop_glue_loc : loc) (traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1431314319_std_ops_ControlFlowunit_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els (UnitSynType) (NeverSynType)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (RefSynType)) : syn_type)) →
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1431314319_std_ops_ControlFlowunit_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1431314319_std_ops_ControlFlowunit_loc @ function_ptr [RefSynType; UnitSynType; ((tuple1_sls (RefSynType)) : syn_type)] (<tag_type> spec! ( *[vlft6; late_lft_0]) : 2 | ( *[Self_ty; F_ty; Item_ty]) : ([Self_rt; F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_try_fold_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec-[] -[])) (unit) ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) (((((ControlFlow_rt)) (unit) (unit)))) (((((ControlFlow_rt)) (unit) (unit)))) (((((ControlFlow_rt)) (unit) (unit)))) (UnitSynType) (((tuple1_sls (RefSynType)) : syn_type)) (((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) (((ControlFlow_els (UnitSynType) (NeverSynType)) : syn_type)) (((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) (traits_iterator_Iterator_all_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Self_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_all_closure0_FnMut_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Self_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs)) (ControlFlowBCasFromResidualControlFlowB_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (ControlFlowBCasFromResidualControlFlowB_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (ControlFlowBCasTry_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (ControlFlowBCasTry_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (ControlFlowBasResidualC_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (drop_glue_trivial_spec_attrs (unit)) (drop_glue_tuple1_spec_attrs (((place_rfnRT (F_rt)) * gname)%type) ((drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type)))) (drop_glue_ControlFlow_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (drop_glue_ControlFlow_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) (drop_glue_ControlFlow_spec_attrs (unit) (unit) ((drop_glue_trivial_spec_attrs (unit))) ((drop_glue_trivial_spec_attrs (unit)))) -[late_lft_0] -[unit_t; (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type) -[] -[(mut_ref vlft6 F_ty)]); (ControlFlow_ty (unit) (unit) -[] -[unit_t; unit_t]); (ControlFlow_ty (unit) (unit) -[] -[unit_t; never_t]); (ControlFlow_ty (unit) (unit) -[] -[unit_t; unit_t])]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_all_def DropGlue_F_drop_glue_loc  traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1431314319_std_ops_ControlFlowunit_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_all_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st DropGlue_Self_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_F_spec_attrs -[ulft_1] -[Self_ty; Item_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_all (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (DropGlue_Self_spec_attrs) (DropGlue_Self_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_spec) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec) (DropGlue_F_spec_attrs) (DropGlue_F_spec))-[ulft_1] -[Self_ty; Item_ty; F_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_all_prelude :=
  unfold traits_iterator_Iterator_all_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_all");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st DropGlue_Self_spec_attrs DropGlue_Self_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec DropGlue_F_spec_attrs DropGlue_F_spec;
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
  start_function "traits_iterator_Iterator_all" ϝ fid ( [ulft_1 [] ] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [ [  p P ] ClosInv ] self ] f ] ) ( p P ClosInv self f );
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
