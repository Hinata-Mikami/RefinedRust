From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFAasPartialOrdREFB_lt_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(PartialEq_A_B_realization : !(trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt))))) `(PartialOrd_A_B_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) PartialEq_A_B_spec_attrs)) `(PartialOrd_A_B_realization : !(trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (B_rt))))) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) `(DropGlue_B_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt))))) (PartialOrd_A_B_lt_loc : loc) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (B_st) →
  PartialOrd_A_B_lt_loc ◁ᵥ{π, MetaNone} PartialOrd_A_B_lt_loc @ function_ptr [RefSynType; RefSynType] (<tag_type> spec_collapse_params _ _ (λ (PartialOrd_A_B_lfts_inst : prod_vec lft PartialOrd_A_B_realization.(trait_ctx_lfts)) (PartialOrd_A_B_tys_inst : plist type PartialOrd_A_B_realization.(trait_ctx_tys)), spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), fn_spec_add_late_pre ((PartialOrd_lt_spec (RRGS:=RRGS) (PartialOrd_A_B_realization.(trait_ctx_spec) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst -[] -[]))  -[late_lft_0; late_lft_1] -[]) (λ π, ((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (PartialOrd_A_B_realization.(trait_ctx_wf) PartialOrd_A_B_lfts_inst PartialOrd_A_B_tys_inst π))%I)) -∗
  typed_function π (REFAasPartialOrdREFB_lt_def PartialOrd_A_B_lt_loc  A_st  B_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), fn_spec_add_late_pre (type_of_REFAasPartialOrdREFB_lt A_rt B_rt A_st B_st PartialEq_A_B_spec_attrs PartialOrd_A_B_spec_attrs DropGlue_A_spec_attrs DropGlue_B_spec_attrs -[ulft_1; ulft_2; ulft_3; ulft_4] -[A_ty; B_ty]) (λ π, ((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (((trait_incl_of_REFAasPartialOrdREFB_lt (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (PartialEq_A_B_realization) (PartialOrd_A_B_spec_attrs) (PartialOrd_A_B_realization) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (DropGlue_B_spec_attrs) (DropGlue_B_realization))-[ulft_1; ulft_2; ulft_3; ulft_4] -[A_ty; B_ty]) π))).
End proof.

Ltac REFAasPartialOrdREFB_lt_prelude :=
  unfold REFAasPartialOrdREFB_lt_lemma;
  set (FN_NAME := FUNCTION_NAME "REFAasPartialOrdREFB_lt");
  intros A_rt B_rt A_st B_st PartialEq_A_B_spec_attrs PartialEq_A_B_realization PartialOrd_A_B_spec_attrs PartialOrd_A_B_realization DropGlue_A_spec_attrs DropGlue_A_realization DropGlue_B_spec_attrs DropGlue_B_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let ulft_3 := fresh "ulft_3" in
  let ulft_4 := fresh "ulft_4" in
  let A_ty := fresh "A_ty" in
  let B_ty := fresh "B_ty" in
  start_function "REFAasPartialOrdREFB_lt" ϝ fid ( [ulft_1 [ulft_2 [ulft_3 [ulft_4 [] ] ] ] ] ) ( [A_ty [B_ty [] ] ] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("ulft_2", ulft_2) :: ("ulft_3", ulft_3) :: ("ulft_4", ulft_4) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ <[
      "B" :=
  existT _ (B_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
