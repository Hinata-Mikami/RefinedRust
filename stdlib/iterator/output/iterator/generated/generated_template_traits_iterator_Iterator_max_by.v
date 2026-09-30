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
Definition traits_iterator_Iterator_max_by_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(F_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(F_st : !syn_type) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt))))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_realization : !(trait_spec_realization (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt))))) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))))))) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_F_drop_glue_loc : loc) (traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2631326319_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (RefSynType)) : syn_type)) →
  DropGlue_F_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_F_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I)) -∗
  traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2631326319_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2631326319_loc @ function_ptr [Self_st; ((tuple1_sls (RefSynType)) : syn_type)] (<tag_type> spec_collapse_params _ _ (λ (traits_iterator_Iterator_Self_lfts_inst : prod_vec lft traits_iterator_Iterator_Self_realization.(trait_ctx_lfts)) (traits_iterator_Iterator_Self_tys_inst : plist type traits_iterator_Iterator_Self_realization.(trait_ctx_tys)), spec! ( *[vlft4]) : 1 | ( *[Self_ty; F_ty; Item_ty]) : ([Self_rt; F_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_reduce_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_realization.(trait_ctx_spec) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst -[] -[])) ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) (((tuple1_sls (RefSynType)) : syn_type)) (traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Self_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_max_by_closure0_FnMut_spec_attrs ((Self_rt)) ((F_rt)) ((Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Self_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs)) (drop_glue_tuple1_spec_attrs (((place_rfnRT (F_rt)) * gname)%type) ((drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type)))) -[] -[(tuple1_ty (((place_rfnRT (F_rt)) * gname)%type) -[] -[(mut_ref vlft4 F_ty)])]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (traits_iterator_Iterator_Self_realization.(trait_ctx_wf) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst π))%I)) -∗
  typed_function π (traits_iterator_Iterator_max_by_def DropGlue_F_drop_glue_loc  traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2631326319_loc  Self_st  Item_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_max_by_base_spec Self_rt Item_rt F_rt Self_st Item_st F_st DropGlue_Self_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs DropGlue_F_spec_attrs -[] -[Self_ty; Item_ty; F_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (((trait_incl_of_traits_iterator_Iterator_max_by (Self_rt) (Item_rt) (F_rt) (Self_st) (Item_st) (F_st) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_realization) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_realization) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization))-[] -[Self_ty; Item_ty; F_ty]) π))).
End proof.

Ltac traits_iterator_Iterator_max_by_prelude :=
  unfold traits_iterator_Iterator_max_by_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_max_by");
  intros Self_rt Item_rt F_rt Self_st Item_st F_st DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_realization FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization DropGlue_F_spec_attrs DropGlue_F_realization;
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
  let compare := fresh "compare" in
  start_function "traits_iterator_Iterator_max_by" ϝ fid ( [] ) ( [Self_ty [Item_ty [F_ty [] ] ] ] ) ( [ [ [  p ClosInv ] self ] compare ] ) ( p ClosInv self compare );
  intros arg_self arg_compare;
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
