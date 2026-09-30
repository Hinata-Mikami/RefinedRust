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
Definition traits_iterator_Iterator_reduce_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt))))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_realization : !(trait_spec_realization (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt))))) `(FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt))))) `(FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) `(FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_F_drop_glue_loc : loc) (DropGlue_Self_drop_glue_loc : loc) (DropGlue_Selfastraits_iterator_Iterator_Item_drop_glue_loc : loc) (std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc : loc) (std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc : loc) (traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc : loc) (traits_iterator_Iterator_Self_next_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((ControlFlow_els (((Option_els (NeverSynType)) : syn_type)) (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Break_sls (((Option_els (NeverSynType)) : syn_type)) (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Continue_sls (((Option_els (NeverSynType)) : syn_type)) (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (NeverSynType)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (Item_st)) : syn_type)) →
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I)) -∗
  DropGlue_Self_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_Self_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I)) -∗
  DropGlue_Selfastraits_iterator_Iterator_Item_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_Selfastraits_iterator_Iterator_Item_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_Selfastraits_iterator_Iterator_Item_lfts_inst : prod_vec lft DropGlue_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_lfts)) (DropGlue_Selfastraits_iterator_Iterator_Item_tys_inst : plist type DropGlue_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_spec) DropGlue_Selfastraits_iterator_Iterator_Item_lfts_inst DropGlue_Selfastraits_iterator_Iterator_Item_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_Selfastraits_iterator_Iterator_Item_realization.(trait_ctx_wf) DropGlue_Selfastraits_iterator_Iterator_Item_lfts_inst DropGlue_Selfastraits_iterator_Iterator_Item_tys_inst π))%I)) -∗
  std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc ◁ᵥ{π, MetaNone} std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc @ function_ptr [((Option_els (NeverSynType)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[Item_ty]) : ([Item_rt] : list RT), let realization := (std_option_OptionTasFromResidual_realization (Item_rt) Item_st DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization) in fn_spec_add_late_pre ((FromResidual_from_residual_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[Item_ty] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[Item_ty] π))%I) -∗
  std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc ◁ᵥ{π, MetaNone} std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc @ function_ptr [((Option_els (Item_st)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[Item_ty]) : ([Item_rt] : list RT), let realization := (std_option_OptionTasTry_realization (Item_rt) Item_st DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization) in fn_spec_add_late_pre ((Try_branch_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[Item_ty] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[Item_ty] π))%I) -∗
  traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc @ function_ptr [Self_st; Item_st; F_st] (<tag_type> spec_collapse_params _ _ (λ (traits_iterator_Iterator_Self_lfts_inst : prod_vec lft traits_iterator_Iterator_Self_realization.(trait_ctx_lfts)) (traits_iterator_Iterator_Self_tys_inst : plist type traits_iterator_Iterator_Self_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[Self_ty; F_ty; Item_ty]) : ([Self_rt; F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_fold_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_realization.(trait_ctx_spec) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst -[] -[])) ((Item_rt)) ((F_rt)) (Item_st) (F_st) FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_F_spec_attrs -[] -[Item_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (traits_iterator_Iterator_Self_realization.(trait_ctx_wf) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst π))%I)) -∗
  traits_iterator_Iterator_Self_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_next_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (traits_iterator_Iterator_Self_lfts_inst : prod_vec lft traits_iterator_Iterator_Self_realization.(trait_ctx_lfts)) (traits_iterator_Iterator_Self_tys_inst : plist type traits_iterator_Iterator_Self_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_realization.(trait_ctx_spec) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (traits_iterator_Iterator_Self_realization.(trait_ctx_wf) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst π))%I)) -∗
  typed_function π (traits_iterator_Iterator_reduce_def DropGlue_F_drop_glue_loc  DropGlue_Self_drop_glue_loc  DropGlue_Selfastraits_iterator_Iterator_Item_drop_glue_loc  std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc  std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc  traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc  traits_iterator_Iterator_Self_next_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_reduce_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st DropGlue_Self_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs DropGlue_F_spec_attrs -[] -[Self_ty; Item_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (((trait_incl_of_traits_iterator_Iterator_reduce (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_realization) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_realization) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_realization) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization))-[] -[Self_ty; Item_ty; F_ty]) π)
  ∗ ((introduce_direct ((let realization := (std_option_OptionTasFromResidual_realization (Item_rt) Item_st DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization) in realization.(trait_ctx_wf) -[] -[Item_ty] π))))
  ∗ ((introduce_direct ((let realization := (std_option_OptionTasTry_realization (Item_rt) Item_st DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization) in realization.(trait_ctx_wf) -[] -[Item_ty] π)))))).
End proof.

Ltac traits_iterator_Iterator_reduce_prelude :=
  unfold traits_iterator_Iterator_reduce_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_reduce");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_realization FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_realization FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_realization DropGlue_F_spec_attrs DropGlue_F_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_reduce" ϝ fid ( [] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [  p ClosInv ] self ] f ] ) ( p ClosInv self f );
  intros arg_self arg_f;
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
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
