From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFmutAasPartialEqREFB_ne_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(B_rt : !RT) `(A_st : !syn_type) `(B_st : !syn_type) `(PartialEq_A_B_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (B_rt) )) `(PartialEq_A_B_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (B_rt)))) `(DropGlue_A_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) `(DropGlue_B_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (PartialEq_A_B_ne_loc : loc) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (B_st) →
  PartialEq_A_B_ne_loc ◁ᵥ{π, MetaNone} PartialEq_A_B_ne_loc @ function_ptr [RefSynType; RefSynType] (<tag_type> spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((PartialEq_ne_spec (RRGS:=RRGS) (PartialEq_A_B_spec-[] -[]))  -[late_lft_0; late_lft_1] -[]) (λ π, (True))%I) -∗
  typed_function π (REFmutAasPartialEqREFB_ne_def PartialEq_A_B_ne_loc  A_st  B_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2; ulft_3; ulft_4]) : 4 | ( *[A_ty; B_ty]) : ([A_rt; B_rt] : list RT), fn_spec_add_late_pre (type_of_REFmutAasPartialEqREFB_ne A_rt B_rt A_st B_st PartialEq_A_B_spec_attrs -[ulft_1; ulft_2; ulft_3; ulft_4] -[A_ty; B_ty]) (λ π, ((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf B_rt B_st B_ty))
  ∗ (⌜((trait_incl_of_REFmutAasPartialEqREFB_ne (A_rt) (B_rt) (A_st) (B_st) (PartialEq_A_B_spec_attrs) (PartialEq_A_B_spec) (DropGlue_A_spec) (DropGlue_B_spec))-[ulft_1; ulft_2; ulft_3; ulft_4] -[A_ty; B_ty])%Z⌝))).
End proof.

Ltac REFmutAasPartialEqREFB_ne_prelude :=
  unfold REFmutAasPartialEqREFB_ne_lemma;
  set (FN_NAME := FUNCTION_NAME "REFmutAasPartialEqREFB_ne");
  intros A_rt B_rt A_st B_st PartialEq_A_B_spec_attrs PartialEq_A_B_spec DropGlue_A_spec DropGlue_B_spec;
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
  start_function "REFmutAasPartialEqREFB_ne" ϝ fid ( [ulft_1 [ulft_2 [ulft_3 [ulft_4 [] ] ] ] ] ) ( [A_ty [B_ty [] ] ] ) ( ? );
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
