From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range Require Export generated_code_range generated_specs_range.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Range_Idx_is_empty_lemma (π : thread_id) : Prop :=
  ∀ `(Idx_rt : !RT) `(Idx_st : !syn_type) `(DropGlue_Idx_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) `(DropGlue_Idx_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Idx_rt))))) `(PartialEq_Idx_Idx_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) )) `(PartialEq_Idx_Idx_realization : !(trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Idx_rt) (Idx_rt))))) `(PartialOrd_Idx_Idx_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) PartialEq_Idx_Idx_spec_attrs)) `(PartialOrd_Idx_Idx_realization : !(trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Idx_rt) (Idx_rt))))) (PartialOrd_Idx_Idx_lt_loc : loc) , 
  syn_type_is_layoutable (Idx_st) →
  syn_type_is_layoutable (((Range_sls (Idx_st)) : syn_type)) →
  PartialOrd_Idx_Idx_lt_loc ◁ᵥ{π, MetaNone} PartialOrd_Idx_Idx_lt_loc @ function_ptr [RefSynType; RefSynType] (<tag_type> spec_collapse_params _ _ (λ (PartialOrd_Idx_Idx_lfts_inst : prod_vec lft PartialOrd_Idx_Idx_realization.(trait_ctx_lfts)) (PartialOrd_Idx_Idx_tys_inst : plist type PartialOrd_Idx_Idx_realization.(trait_ctx_tys)), spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[Idx_ty]) : ([Idx_rt] : list RT), fn_spec_add_late_pre ((PartialOrd_lt_spec (RRGS:=RRGS) (PartialOrd_Idx_Idx_realization.(trait_ctx_spec) PartialOrd_Idx_Idx_lfts_inst PartialOrd_Idx_Idx_tys_inst -[] -[]))  -[late_lft_0; late_lft_1] -[]) (λ π, ((typaram_wf Idx_rt Idx_st Idx_ty))
  ∗ (PartialOrd_Idx_Idx_realization.(trait_ctx_wf) PartialOrd_Idx_Idx_lfts_inst PartialOrd_Idx_Idx_tys_inst π))%I)) -∗
  typed_function π (Range_Idx_is_empty_def PartialOrd_Idx_Idx_lt_loc  Idx_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Idx_ty]) : ([Idx_rt] : list RT), fn_spec_add_late_pre (type_of_Range_Idx_is_empty Idx_rt Idx_st DropGlue_Idx_spec_attrs PartialEq_Idx_Idx_spec_attrs PartialOrd_Idx_Idx_spec_attrs -[ulft_1] -[Idx_ty]) (λ π, ((typaram_wf Idx_rt Idx_st Idx_ty))
  ∗ (((trait_incl_of_Range_Idx_is_empty (Idx_rt) (Idx_st) (DropGlue_Idx_spec_attrs) (DropGlue_Idx_realization) (PartialEq_Idx_Idx_spec_attrs) (PartialEq_Idx_Idx_realization) (PartialOrd_Idx_Idx_spec_attrs) (PartialOrd_Idx_Idx_realization))-[ulft_1] -[Idx_ty]) π))).
End proof.

Ltac Range_Idx_is_empty_prelude :=
  unfold Range_Idx_is_empty_lemma;
  set (FN_NAME := FUNCTION_NAME "Range_Idx_is_empty");
  intros Idx_rt Idx_st DropGlue_Idx_spec_attrs DropGlue_Idx_realization PartialEq_Idx_Idx_spec_attrs PartialEq_Idx_Idx_realization PartialOrd_Idx_Idx_spec_attrs PartialOrd_Idx_Idx_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let Idx_ty := fresh "Idx_ty" in
  let self := fresh "self" in
  start_function "Range_Idx_is_empty" ϝ fid ( [ulft_1 [] ] ) ( [Idx_ty [] ] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Idx" :=
  existT _ (Idx_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
