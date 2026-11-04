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
Definition traits_iterator_Iterator_max_by_closure0_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_realization : !(trait_spec_realization (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt))))) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))))))) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))))))) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt))))) (max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc : loc) (max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc_linking : spec_with 1 [F_rt; traits_iterator_Iterator_Self_Item_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (traits_iterator_Iterator_Self_Item_st) →
  syn_type_is_layoutable (((tuple1_sls (RefSynType)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) →
  max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc ◁ᵥ{π, MetaNone} max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc @ function_ptr [traits_iterator_Iterator_Self_Item_st; traits_iterator_Iterator_Self_Item_st; RefSynType] (<tag_type> spec! ( *[vlft7]) : 1 | ( *[F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (type_of_max_by (RRGS:=RRGS) ((traits_iterator_Iterator_Self_Item_rt)) (((place_rfnRT (F_rt)) * gname)%type) (traits_iterator_Iterator_Self_Item_st) (RefSynType) (REFmutFasFnOnceA_spec_attrs ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((F_rt)) ((((Ordering_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) ((drop_glue_tuple2_spec_attrs ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))))) (DropGlue_F_spec_attrs) ((drop_glue_trivial_spec_attrs ((((Ordering_rt))))))) DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs (drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type)) -[] -[traits_iterator_Iterator_Self_Item_ty; (mut_ref vlft7 F_ty)]) (λ π, ((typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (from_assumption_hint (max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc_linking -[vlft7] -[F_ty; traits_iterator_Iterator_Self_Item_ty] π)))%I) -∗
  typed_function π (traits_iterator_Iterator_max_by_closure0_def max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc  Self_st  F_st  traits_iterator_Iterator_Self_Item_st  ) (<tag_type> spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), fn_spec_add_late_pre (type_of_traits_iterator_Iterator_max_by_closure0 Self_rt F_rt traits_iterator_Iterator_Self_Item_rt Self_st F_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Self_spec_attrs DropGlue_F_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs -[ulft1; ulft2] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf traits_iterator_Iterator_Self_Item_rt traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_ty))
  ∗ (((trait_incl_of_traits_iterator_Iterator_max_by_closure0 (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_realization) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_F_spec_attrs) (DropGlue_F_realization) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_realization))-[ulft1; ulft2] -[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) π)
  ∗ (□ (∀ (vlft7 : lft), max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc_linking -[vlft7] -[F_ty; traits_iterator_Iterator_Self_Item_ty] π)))).
End proof.

Ltac traits_iterator_Iterator_max_by_closure0_prelude :=
  unfold traits_iterator_Iterator_max_by_closure0_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_max_by_closure0");
  intros Self_rt F_rt traits_iterator_Iterator_Self_Item_rt Self_st F_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_realization FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_realization DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_F_spec_attrs DropGlue_F_realization DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft1 := fresh "ulft1" in
  let ulft2 := fresh "ulft2" in
  let Self_ty := fresh "Self_ty" in
  let F_ty := fresh "F_ty" in
  let traits_iterator_Iterator_Self_Item_ty := fresh "traits_iterator_Iterator_Self_Item_ty" in
  let capture_compare_ := fresh "capture_compare_" in
  let _γcapture_compare_g := fresh "_γcapture_compare_g" in
  let __γclos := fresh "__γclos" in
  let pclos := fresh "pclos" in
  let a := fresh "a" in
  let b := fresh "b" in
  start_function "traits_iterator_Iterator_max_by_closure0" ϝ fid ( [ulft1 [ulft2 [] ] ] ) ( [Self_ty [F_ty [traits_iterator_Iterator_Self_Item_ty [] ] ] ] ) ( [ [ [ [ [  capture_compare_ _γcapture_compare_g ] __γclos ] pclos ] a ] b ] ) ( capture_compare_ _γcapture_compare_g __γclos pclos a b );
  intros arg___1 arg_a arg_b;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft1", ulft1) :: ("ulft2", ulft2) :: ("_flft", ϝ) :: ("static", static) :: [] );
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
