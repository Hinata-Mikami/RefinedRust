From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition PartialEq_ne_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Rhs_rt : !RT) `(Self_st : !syn_type) `(Rhs_st : !syn_type) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_Rhs_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Rhs_rt) )) `(DropGlue_Rhs_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Rhs_rt))))) `(PartialEq_Self_Rhs_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) `(PartialEq_Self_Rhs_realization : !(trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt))))) (PartialEq_Self_Rhs_eq_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Rhs_st) →
  PartialEq_Self_Rhs_eq_loc ◁ᵥ{π, MetaNone} PartialEq_Self_Rhs_eq_loc @ function_ptr [RefSynType; RefSynType] (<tag_type> spec_collapse_params _ _ (λ (PartialEq_Self_Rhs_lfts_inst : prod_vec lft PartialEq_Self_Rhs_realization.(trait_ctx_lfts)) (PartialEq_Self_Rhs_tys_inst : plist type PartialEq_Self_Rhs_realization.(trait_ctx_tys)), spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), fn_spec_add_late_pre ((PartialEq_eq_spec (RRGS:=RRGS) (PartialEq_Self_Rhs_realization.(trait_ctx_spec) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst -[] -[]))  -[late_lft_0; late_lft_1] -[]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Rhs_rt Rhs_st Rhs_ty))
  ∗ (PartialEq_Self_Rhs_realization.(trait_ctx_wf) PartialEq_Self_Rhs_lfts_inst PartialEq_Self_Rhs_tys_inst π))%I)) -∗
  typed_function π (PartialEq_ne_def PartialEq_Self_Rhs_eq_loc  Self_st  Rhs_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), fn_spec_add_late_pre (PartialEq_ne_base_spec Self_rt Rhs_rt Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Rhs_spec_attrs PartialEq_Self_Rhs_spec_attrs -[ulft_1; ulft_2] -[Self_ty; Rhs_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Rhs_rt Rhs_st Rhs_ty))
  ∗ (((trait_incl_of_PartialEq_ne (Self_rt) (Rhs_rt) (Self_st) (Rhs_st) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_Rhs_spec_attrs) (DropGlue_Rhs_realization) (PartialEq_Self_Rhs_spec_attrs) (PartialEq_Self_Rhs_realization))-[ulft_1; ulft_2] -[Self_ty; Rhs_ty]) π))).
End proof.

Ltac PartialEq_ne_prelude :=
  unfold PartialEq_ne_lemma;
  set (FN_NAME := FUNCTION_NAME "PartialEq_ne");
  intros Self_rt Rhs_rt Self_st Rhs_st DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_Rhs_spec_attrs DropGlue_Rhs_realization PartialEq_Self_Rhs_spec_attrs PartialEq_Self_Rhs_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let Self_ty := fresh "Self_ty" in
  let Rhs_ty := fresh "Rhs_ty" in
  let self := fresh "self" in
  let other := fresh "other" in
  start_function "PartialEq_ne" ϝ fid ( [ulft_1 [ulft_2 [] ] ] ) ( [Self_ty [Rhs_ty [] ] ] ) ( [  self other ] ) ( self other );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("ulft_2", ulft_2) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "Rhs" :=
  existT _ (Rhs_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
