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
Definition traits_iterator_Iterator_fold_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(B_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(B_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) `(FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt)))) `(FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) `(FnMut_F_BSelfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt)))) (FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc : loc) (traits_iterator_Iterator_Self_next_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (B_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (B_st) (Item_st)) : syn_type)) →
  FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc ◁ᵥ{π, MetaNone} FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc @ function_ptr [PtrSynType; ((tuple2_sls (B_st) (Item_st)) : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[B_ty; F_ty; B_ty; Item_ty; B_ty]) : ([B_rt; F_rt; B_rt; Item_rt; B_rt] : list RT), fn_spec_add_late_pre ((FnMut_call_mut_spec (RRGS:=RRGS) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec <INST!>))   <LFT> late_lft_0 <INST!>) (λ π, ((typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf B_rt B_st B_ty)))%I) -∗
  traits_iterator_Iterator_Self_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_next_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_spec <INST!>))   <LFT> late_lft_0 <INST!>) (λ π, (True))%I) -∗
  typed_function π (traits_iterator_Iterator_fold_def FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc  traits_iterator_Iterator_Self_next_loc  Self_st  Item_st  B_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([Self_rt; Item_rt; B_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_fold_base_spec Self_rt Item_rt B_rt F_rt Self_st Item_st B_st F_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs  <TY> Self_ty <TY> Item_ty <TY> B_ty <TY> F_ty <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_fold (Self_rt) (Item_rt) (B_rt) (F_rt) (Self_st) (Item_st) (B_st) (F_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec)) <TY> Self_ty <TY> Item_ty <TY> B_ty <TY> F_ty <INST!>)%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_fold_prelude :=
  unfold traits_iterator_Iterator_fold_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_fold");
  intros Self_rt Item_rt B_rt F_rt Self_st Item_st B_st F_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let B_ty := fresh "B_ty" in
  let F_ty := fresh "F_ty" in
  let p := fresh "p" in
  let ClosInv := fresh "ClosInv" in
  let self := fresh "self" in
  let init := fresh "init" in
  let f := fresh "f" in
  start_function "traits_iterator_Iterator_fold" ϝ ( [] ) ( [Self_ty [Item_ty [B_ty [F_ty [] ] ] ] ] ) ( [ [ [ [  p ClosInv ] self ] init ] f ] ) (  p ClosInv self init f );
  intros arg_self arg_init arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyCons ("_bb1", (["self"; "f"; "accum"], ["init"; "x"], ["__0"; "__5"; "__6"; "__7"; "__8"; "__9"; "__12"; "__13"; "__14"; "__15"; "__16"; "__17"; "__18"; "__19"], wrap_inv (λ (_params: ((_))) (_var_self: (place_rfnRT (Self_rt))) (_var_f: (place_rfnRT (F_rt))) (_var_accum: (place_rfnRT (B_rt))), let '(init_state) := _params in ((∃ (seq: _) (self: _) (accum: _) (f: _), (⌜(_var_self = ($# self))%Z⌝)
  ∗ (⌜(_var_accum = ($# accum))%Z⌝)
  ∗ (⌜(_var_f = ($# f))%Z⌝)
  ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p init_state seq self)
  ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)
  ∗ (ClosInv π accum seq self f))%I) : (iProp Σ)), wrap_inv (λ (L : llctx), True%I : iProp Σ), None)) $ PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
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
  unfold_generic_inst; simpl.
