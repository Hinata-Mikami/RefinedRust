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
Definition traits_iterator_Iterator_all_closure0_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (FnMut_F_Selfastraits_iterator_Iterator_Item_call_mut_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (traits_iterator_Iterator_Self_Item_st) →
  syn_type_is_layoutable (((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Break_sls (UnitSynType) (UnitSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Continue_sls (UnitSynType) (UnitSynType)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (RefSynType)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type)) →
  FnMut_F_Selfastraits_iterator_Iterator_Item_call_mut_loc ◁ᵥ{π, MetaNone} FnMut_F_Selfastraits_iterator_Iterator_Item_call_mut_loc @ function_ptr [RefSynType; ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre ((FnMut_call_mut_spec (RRGS:=RRGS) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec-[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_all_closure0_def FnMut_F_Selfastraits_iterator_Iterator_Item_call_mut_loc  Self_st  F_st  traits_iterator_Iterator_Self_Item_st  ) (<tag_type> spec! ( *[ulft1; ulft3]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (type_of_traits_iterator_Iterator_all_closure0 Self_rt F_rt traits_iterator_Iterator_Self_Item_rt Self_st F_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs -[ulft1; ulft3] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_all_closure0 (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec) (DropGlue_Self_spec) (DropGlue_F_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec))-[ulft1; ulft3] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_all_closure0_prelude :=
  unfold traits_iterator_Iterator_all_closure0_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_all_closure0");
  intros Self_rt F_rt traits_iterator_Iterator_Self_Item_rt Self_st F_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec DropGlue_Self_spec DropGlue_F_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft1 := fresh "ulft1" in
  let ulft3 := fresh "ulft3" in
  let Self_ty := fresh "Self_ty" in
  let F_ty := fresh "F_ty" in
  let traits_iterator_Iterator_Self_Item_ty := fresh "traits_iterator_Iterator_Self_Item_ty" in
  let capture_f_ := fresh "capture_f_" in
  let _γf := fresh "_γf" in
  let __γclos := fresh "__γclos" in
  let pclos := fresh "pclos" in
  let _arg_0 := fresh "_arg_0" in
  let b := fresh "b" in
  start_function "traits_iterator_Iterator_all_closure0" ϝ fid ( [ulft1 [ulft3 [] ] ] ) ( [Self_ty [F_ty [traits_iterator_Iterator_Self_Item_ty [] ] ] ] ) ( [ [ [ [ [  capture_f_ _γf ] __γclos ] pclos ] _arg_0 ] b ] ) ( capture_f_ _γf __γclos pclos _arg_0 b );
  intros arg___1 arg___2 arg_b;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft1", ulft1) :: ("ulft3", ulft3) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ <[
      "traits_iterator_Iterator_Self_Item" :=
  existT _ (traits_iterator_Iterator_Self_Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
