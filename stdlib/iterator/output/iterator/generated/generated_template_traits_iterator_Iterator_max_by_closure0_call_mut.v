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
Definition traits_iterator_Iterator_max_by_closure0_call_mut_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec : !(spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec : !(spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_max_by_closure0_loc : loc) , 
  syn_type_is_layoutable (((tuple1_sls (RefSynType)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) →
  syn_type_is_layoutable (traits_iterator_Iterator_Self_Item_st) →
  traits_iterator_Iterator_max_by_closure0_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_max_by_closure0_loc @ function_ptr [RefSynType; traits_iterator_Iterator_Self_Item_st; traits_iterator_Iterator_Self_Item_st] (<tag_type> spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (type_of_traits_iterator_Iterator_max_by_closure0 (RRGS:=RRGS) ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs -[ulft1; ulft2] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_max_by_closure0_call_mut_code traits_iterator_Iterator_max_by_closure0_loc  Self_st  F_st  traits_iterator_Iterator_Self_Item_st  ) (<tag_type> spec! ( *[ulft1; _ref_lft]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_max_by_closure0_call_mut_spec Self_rt F_rt traits_iterator_Iterator_Self_Item_rt Self_st F_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs -[ulft1; _ref_lft] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (⌜((traits_iterator_Iterator_max_by_closure0_call_mut_trait_req_incl (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec) (DropGlue_Self_spec) (DropGlue_F_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec))-[ulft1; _ref_lft] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_max_by_closure0_call_mut_prelude :=
  unfold traits_iterator_Iterator_max_by_closure0_call_mut_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_max_by_closure0_call_mut");
  intros Self_rt F_rt traits_iterator_Iterator_Self_Item_rt Self_st F_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec DropGlue_Self_spec DropGlue_F_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft1 := fresh "ulft1" in
  let _ref_lft := fresh "_ref_lft" in
  let Self_ty := fresh "Self_ty" in
  let F_ty := fresh "F_ty" in
  let traits_iterator_Iterator_Self_Item_ty := fresh "traits_iterator_Iterator_Self_Item_ty" in
  start_function "traits_iterator_Iterator_max_by_closure0_call_mut" ϝ ( [ulft1 [_ref_lft [] ] ] ) ( [Self_ty [F_ty [traits_iterator_Iterator_Self_Item_ty [] ] ] ] ) ( ? );
  intros arg_self arg_args;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft1" ulft1 $ named_lft_update "_ref_lft" _ref_lft $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
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
