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
Definition traits_iterator_Iterator_try_fold_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(B_rt : !RT) `(F_rt : !RT) `(R_rt : !RT) `(Try_R_Residual_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(B_st : !syn_type) `(F_st : !syn_type) `(R_st : !syn_type) `(Try_R_Residual_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt)))) `(FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) `(FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt)))) `(FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs : !(FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) `(FromResidual_R_Rasstd_ops_Try_Residual_spec : !(spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt)))) `(FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) `(FnMut_F_BSelfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt)))) `(Try_R_spec_attrs : !(Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) `(Try_R_spec : !(spec_with 0 [] (Try_spec (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt)))) `(DropGlue_B_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) `(DropGlue_R_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt)))) `(DropGlue_Rasstd_ops_Try_Residual_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Try_R_Residual_rt)))) (DropGlue_F_drop_glue_loc : loc) (FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc : loc) (FromResidual_R_Rasstd_ops_Try_Residual_from_residual_loc : loc) (Try_R_branch_loc : loc) (Try_R_from_output_loc : loc) (traits_iterator_Iterator_Self_next_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (B_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (R_st) →
  syn_type_is_layoutable (((ControlFlow_els (Try_R_Residual_st) (B_st)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Break_sls (Try_R_Residual_st) (B_st)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Continue_sls (Try_R_Residual_st) (B_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (B_st) (Item_st)) : syn_type)) →
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc ◁ᵥ{π, MetaNone} FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc @ function_ptr [RefSynType; ((tuple2_sls (B_st) (Item_st)) : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[B_ty; F_ty; R_ty; Item_ty; R_ty]) : ([B_rt; F_rt; R_rt; Item_rt; R_rt] : list RT), fn_spec_add_late_pre ((FnMut_call_mut_spec (RRGS:=RRGS) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec-[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf R_rt R_st R_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf R_rt R_st R_ty)))%I) -∗
  FromResidual_R_Rasstd_ops_Try_Residual_from_residual_loc ◁ᵥ{π, MetaNone} FromResidual_R_Rasstd_ops_Try_Residual_from_residual_loc @ function_ptr [Try_R_Residual_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((FromResidual_from_residual_spec (RRGS:=RRGS) (FromResidual_R_Rasstd_ops_Try_Residual_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  Try_R_branch_loc ◁ᵥ{π, MetaNone} Try_R_branch_loc @ function_ptr [R_st] (<tag_type> spec! ( *[]) : 0 | ( *[R_ty; Try_R_Residual_ty]) : ([R_rt; Try_R_Residual_rt] : list RT), fn_spec_add_late_pre ((Try_branch_spec (RRGS:=RRGS) (Try_R_spec-[] -[]))  -[] -[]) (λ π, ((typaram_wf R_rt R_st R_ty)
  ∗ (typaram_wf Try_R_Residual_rt Try_R_Residual_st Try_R_Residual_ty)))%I) -∗
  Try_R_from_output_loc ◁ᵥ{π, MetaNone} Try_R_from_output_loc @ function_ptr [B_st] (<tag_type> spec! ( *[]) : 0 | ( *[R_ty; Try_R_Residual_ty]) : ([R_rt; Try_R_Residual_rt] : list RT), fn_spec_add_late_pre ((Try_from_output_spec (RRGS:=RRGS) (Try_R_spec-[] -[]))  -[] -[]) (λ π, ((typaram_wf R_rt R_st R_ty)
  ∗ (typaram_wf Try_R_Residual_rt Try_R_Residual_st Try_R_Residual_ty)))%I) -∗
  traits_iterator_Iterator_Self_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_next_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec-[] -[]))  -[late_lft_0] -[]) (λ π, (True))%I) -∗
  typed_function π (traits_iterator_Iterator_try_fold_def DropGlue_F_drop_glue_loc  FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc  FromResidual_R_Rasstd_ops_Try_Residual_from_residual_loc  Try_R_branch_loc  Try_R_from_output_loc  traits_iterator_Iterator_Self_next_loc  Self_st  Item_st  B_st  F_st  R_st  Try_R_Residual_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; B_ty; F_ty; R_ty; Try_R_Residual_ty]) : ([Self_rt; Item_rt; B_rt; F_rt; R_rt; Try_R_Residual_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_try_fold_base_spec Self_rt Item_rt B_rt F_rt R_rt Try_R_Residual_rt Self_st Item_st B_st F_st R_st Try_R_Residual_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs Try_R_spec_attrs -[ulft_1] -[Self_ty; Item_ty; B_ty; F_ty; R_ty; Try_R_Residual_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf R_rt R_st R_ty)
  ∗ (typaram_wf Try_R_Residual_rt Try_R_Residual_st Try_R_Residual_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_try_fold (Self_rt) (Item_rt) (B_rt) (F_rt) (R_rt) (Try_R_Residual_rt) (Self_st) (Item_st) (B_st) (F_st) (R_st) (Try_R_Residual_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (DropGlue_Self_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs) (FromResidual_R_Rasstd_ops_Try_Residual_spec) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec) (Try_R_spec_attrs) (Try_R_spec) (DropGlue_B_spec) (DropGlue_F_spec) (DropGlue_R_spec) (DropGlue_Rasstd_ops_Try_Residual_spec))-[ulft_1] -[Self_ty; Item_ty; B_ty; F_ty; R_ty; Try_R_Residual_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_try_fold_prelude :=
  unfold traits_iterator_Iterator_try_fold_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_try_fold");
  intros Self_rt Item_rt B_rt F_rt R_rt Try_R_Residual_rt Self_st Item_st B_st F_st R_st Try_R_Residual_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec DropGlue_Self_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec Try_R_spec_attrs Try_R_spec DropGlue_B_spec DropGlue_F_spec DropGlue_R_spec DropGlue_Rasstd_ops_Try_Residual_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let B_ty := fresh "B_ty" in
  let F_ty := fresh "F_ty" in
  let R_ty := fresh "R_ty" in
  let Try_R_Residual_ty := fresh "Try_R_Residual_ty" in
  let p := fresh "p" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let init := fresh "init" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_try_fold" ϝ ( [ulft_1 [] ] ) ( [Self_ty [Item_ty [B_ty [F_ty [R_ty [Try_R_Residual_ty [] ] ] ] ] ] ] ) ( [ [ [ [  p ClosInv ] self ] init ] f ] ) ( p ClosInv self init f );
  intros arg_self arg_init arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyCons ("_bb1", (["self"; "f"; "accum"], ["init"; "x"; "residual"; "val"; "__28"], ["__0"; "__5"; "__6"; "__7"; "__8"; "__9"; "__12"; "__13"; "__14"; "__15"; "__16"; "__17"; "__18"; "__19"; "__21"; "__22"; "__24"; "__25"; "__26"; "__27"], wrap_inv (λ (_params: ((_ * _))) (_var_self: (place_rfnRT ((place_rfnRT (Self_rt)) * gname)%type)) (_var_f: (place_rfnRT (F_rt))) (_var_accum: (place_rfnRT (B_rt))), let '(γ, init_state) := _params in ((∃ (seq: _) (self: _) (accum: _) (f: _), (⌜(_var_self = ($# self))%Z⌝)
  ∗ (⌜(_var_accum = ($# accum))%Z⌝)
  ∗ (⌜(_var_f = ($# f))%Z⌝)
  ∗ (⌜(self.ghost = γ)%Z⌝)
  ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p init_state seq self.cur)
  ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)
  ∗ (ClosInv π (Ok accum) seq self.cur f))%I) : (iProp Σ)), wrap_inv (λ (L : llctx), True%I : iProp Σ), None)) $ PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
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
      ]>%E $ <[
      "R" :=
  existT _ (R_ty)
      ]>%E $ <[
      "Try_R_Residual" :=
  existT _ (Try_R_Residual_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
