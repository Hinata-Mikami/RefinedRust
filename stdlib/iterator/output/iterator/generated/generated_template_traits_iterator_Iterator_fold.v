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
Definition traits_iterator_Iterator_fold_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(B_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(B_st : !syn_type) `(F_st : !syn_type) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt))))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_realization : !(trait_spec_realization (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt))))) `(FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) `(FnOnce_F_BSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt))))) `(FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) `(FnMut_F_BSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt))))) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) `(DropGlue_B_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_B_drop_glue_loc : loc) (DropGlue_F_drop_glue_loc : loc) (DropGlue_Self_drop_glue_loc : loc) (FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc : loc) (traits_iterator_Iterator_Self_next_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (B_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (B_st) (Item_st)) : syn_type)) →
  DropGlue_B_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_B_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_B_lfts_inst : prod_vec lft DropGlue_B_realization.(trait_ctx_lfts)) (DropGlue_B_tys_inst : plist type DropGlue_B_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_B_realization.(trait_ctx_spec) DropGlue_B_lfts_inst DropGlue_B_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_B_realization.(trait_ctx_wf) DropGlue_B_lfts_inst DropGlue_B_tys_inst π))%I)) -∗
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I)) -∗
  DropGlue_Self_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_Self_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π))%I)) -∗
  FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc ◁ᵥ{π, MetaNone} FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc @ function_ptr [RefSynType; ((tuple2_sls (B_st) (Item_st)) : syn_type)] (<tag_type> spec_collapse_params _ _ (λ (FnMut_F_BSelfastraits_iterator_Iterator_Item_lfts_inst : prod_vec lft FnMut_F_BSelfastraits_iterator_Iterator_Item_realization.(trait_ctx_lfts)) (FnMut_F_BSelfastraits_iterator_Iterator_Item_tys_inst : plist type FnMut_F_BSelfastraits_iterator_Iterator_Item_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[B_ty; F_ty; B_ty; Item_ty]) : ([B_rt; F_rt; B_rt; Item_rt] : list RT), fn_spec_add_late_pre ((FnMut_call_mut_spec (RRGS:=RRGS) (FnMut_F_BSelfastraits_iterator_Iterator_Item_realization.(trait_ctx_spec) FnMut_F_BSelfastraits_iterator_Iterator_Item_lfts_inst FnMut_F_BSelfastraits_iterator_Iterator_Item_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (FnMut_F_BSelfastraits_iterator_Iterator_Item_realization.(trait_ctx_wf) FnMut_F_BSelfastraits_iterator_Iterator_Item_lfts_inst FnMut_F_BSelfastraits_iterator_Iterator_Item_tys_inst π))%I)) -∗
  traits_iterator_Iterator_Self_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_next_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (traits_iterator_Iterator_Self_lfts_inst : prod_vec lft traits_iterator_Iterator_Self_realization.(trait_ctx_lfts)) (traits_iterator_Iterator_Self_tys_inst : plist type traits_iterator_Iterator_Self_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_realization.(trait_ctx_spec) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (traits_iterator_Iterator_Self_realization.(trait_ctx_wf) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst π))%I)) -∗
  typed_function π (traits_iterator_Iterator_fold_def DropGlue_B_drop_glue_loc  DropGlue_F_drop_glue_loc  DropGlue_Self_drop_glue_loc  FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc  traits_iterator_Iterator_Self_next_loc  Self_st  Item_st  B_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([Self_rt; Item_rt; B_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_fold_base_spec Self_rt Item_rt B_rt F_rt Self_st Item_st B_st F_st DropGlue_Self_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs DropGlue_B_spec_attrs DropGlue_F_spec_attrs -[] -[Self_ty; Item_ty; B_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (((trait_incl_of_traits_iterator_Iterator_fold (Self_rt) (Item_rt) (B_rt) (F_rt) (Self_st) (Item_st) (B_st) (F_st) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_realization) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_realization) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_realization) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_realization) (DropGlue_B_spec_attrs) (DropGlue_B_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization))-[] -[Self_ty; Item_ty; B_ty; F_ty]) π))).
End proof.

Ltac traits_iterator_Iterator_fold_prelude :=
  unfold traits_iterator_Iterator_fold_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_fold");
  intros Self_rt Item_rt B_rt F_rt Self_st Item_st B_st F_st DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_realization FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_BSelfastraits_iterator_Iterator_Item_realization FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_realization DropGlue_B_spec_attrs DropGlue_B_realization DropGlue_F_spec_attrs DropGlue_F_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let B_ty := fresh "B_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let init := fresh "init" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_fold" ϝ fid ( [] ) ( [Self_ty [Item_ty [B_ty [F_ty [] ] ] ] ] ) ( [ [ [ [  p ClosInv ] self ] init ] f ] ) ( p ClosInv self init f );
  intros arg_self arg_init arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyCons ("_bb1", (["self"; "f"; "accum"], ["init"; "x"; "__20"], ["__0"; "__5"; "__6"; "__7"; "__8"; "__9"; "__12"; "__13"; "__14"; "__15"; "__16"; "__17"; "__18"; "__19"], wrap_inv (λ (_params: ((_))) (_var_self: (place_rfnRT (Self_rt))) (_var_f: (place_rfnRT (F_rt))) (_var_accum: (place_rfnRT (B_rt))), let '(init_state) := _params in ((∃ (seq: _) (self: _) (accum: _) (f: _), (⌜(_var_self = ($# self))%Z⌝)
  ∗ (⌜(_var_accum = ($# accum))%Z⌝)
  ∗ (⌜(_var_f = ($# f))%Z⌝)
  ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p init_state seq self)
  ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)
  ∗ (ClosInv π accum seq self f))%I) : (iProp Σ)), wrap_inv (λ (L : llctx), True%I : iProp Σ), None)) $ PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
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
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
