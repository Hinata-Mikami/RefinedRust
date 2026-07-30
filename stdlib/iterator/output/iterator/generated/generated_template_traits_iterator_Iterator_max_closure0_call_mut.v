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
Definition traits_iterator_Iterator_max_closure0_call_mut_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Eq_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_max_closure0_loc : loc) , 
  syn_type_is_layoutable (UnitSynType) →
  syn_type_is_layoutable (((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) →
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  traits_iterator_Iterator_max_closure0_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_max_closure0_loc @ function_ptr [RefSynType; RefSynType; RefSynType] (<tag_type> spec! ( *[ulft_1; ulft_2; ulft3]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (type_of_traits_iterator_Iterator_max_closure0 (RRGS:=RRGS) ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (traits_iterator_Iterator_Self_Item_st) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs -[ulft_1; ulft_2; ulft3] -[Self_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_max_closure0_call_mut_code traits_iterator_Iterator_max_closure0_loc  Self_st  traits_iterator_Iterator_Self_Item_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2; _ref_lft]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_max_closure0_call_mut_spec Self_rt traits_iterator_Iterator_Self_Item_rt Self_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs -[ulft_1; ulft_2; _ref_lft] -[Self_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (⌜((traits_iterator_Iterator_max_closure0_call_mut_trait_req_incl (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (traits_iterator_Iterator_Self_Item_st) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec) (DropGlue_Self_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec))-[ulft_1; ulft_2; _ref_lft] -[Self_ty; traits_iterator_Iterator_Self_Item_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_max_closure0_call_mut_prelude :=
  unfold traits_iterator_Iterator_max_closure0_call_mut_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_max_closure0_call_mut");
  intros Self_rt traits_iterator_Iterator_Self_Item_rt Self_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec Eq_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec Ord_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec DropGlue_Self_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let _ref_lft := fresh "_ref_lft" in
  let Self_ty := fresh "Self_ty" in
  let traits_iterator_Iterator_Self_Item_ty := fresh "traits_iterator_Iterator_Self_Item_ty" in
  start_function "traits_iterator_Iterator_max_closure0_call_mut" ϝ ( [ulft_1 [ulft_2 [_ref_lft [] ] ] ] ) ( [Self_ty [traits_iterator_Iterator_Self_Item_ty [] ] ] ) ( ? );
  intros arg_self arg_args;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_ref_lft" _ref_lft $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "traits_iterator_Iterator_Self_Item" :=
  existT _ (traits_iterator_Iterator_Self_Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
