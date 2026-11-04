From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map skip step step_by take.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition traits_iterator_Iterator_max_closure0_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt))))) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Eq_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt))))) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt))))) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt))))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_realization : !(trait_spec_realization (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt))))) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt))))) (Ord_Selfastraits_iterator_Iterator_Item_cmp_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (traits_iterator_Iterator_Self_Item_st) →
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) →
  Ord_Selfastraits_iterator_Iterator_Item_cmp_loc ◁ᵥ{π, MetaNone} Ord_Selfastraits_iterator_Iterator_Item_cmp_loc @ function_ptr [RefSynType; RefSynType] (<tag_type> spec_collapse_params _ _ (λ (Ord_Selfastraits_iterator_Iterator_Item_lfts_inst : prod_vec lft Ord_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_lfts)) (Ord_Selfastraits_iterator_Iterator_Item_tys_inst : plist type Ord_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_tys)), spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[traits_iterator_Iterator_Self_Item_ty]) : ([traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre ((Ord_cmp_spec (RRGS:=RRGS) (Ord_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_spec) Ord_Selfastraits_iterator_Iterator_Item_lfts_inst Ord_Selfastraits_iterator_Iterator_Item_tys_inst -[] -[]))  -[late_lft_0; late_lft_1] -[]) (λ π, ((typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (Ord_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_wf) Ord_Selfastraits_iterator_Iterator_Item_lfts_inst Ord_Selfastraits_iterator_Iterator_Item_tys_inst π))%I)) -∗
  typed_function π (traits_iterator_Iterator_max_closure0_def Ord_Selfastraits_iterator_Iterator_Item_cmp_loc  Self_st  traits_iterator_Iterator_Self_Item_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2; ulft3]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (type_of_traits_iterator_Iterator_max_closure0 Self_rt traits_iterator_Iterator_Self_Item_rt Self_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs DropGlue_Self_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs -[ulft_1; ulft_2; ulft3] -[Self_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (((trait_incl_of_traits_iterator_Iterator_max_closure0 (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (traits_iterator_Iterator_Self_Item_st) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_realization) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_realization) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_realization) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_realization) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_realization) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_realization))-[ulft_1; ulft_2; ulft3] -[Self_ty; traits_iterator_Iterator_Self_Item_ty]) π))).
End proof.

Ltac traits_iterator_Iterator_max_closure0_prelude :=
  unfold traits_iterator_Iterator_max_closure0_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_max_closure0");
  intros Self_rt traits_iterator_Iterator_Self_Item_rt Self_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_realization Eq_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_realization PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_realization Ord_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_realization traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_realization DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let ulft3 := fresh "ulft3" in
  let Self_ty := fresh "Self_ty" in
  let traits_iterator_Iterator_Self_Item_ty := fresh "traits_iterator_Iterator_Self_Item_ty" in
  let __γclos := fresh "__γclos" in
  let a := fresh "a" in
  let b := fresh "b" in
  start_function "traits_iterator_Iterator_max_closure0" ϝ fid ( [ulft_1 [ulft_2 [ulft3 [] ] ] ] ) ( [Self_ty [traits_iterator_Iterator_Self_Item_ty [] ] ] ) ( [ [  __γclos a ] b ] ) ( __γclos a b );
  intros arg___1 arg_a arg_b;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("ulft_2", ulft_2) :: ("ulft3", ulft3) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "traits_iterator_Iterator_Self_Item" :=
  existT _ (traits_iterator_Iterator_Self_Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
