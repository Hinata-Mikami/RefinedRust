From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition PartialOrd_gt_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Rhs_rt : !RT) `(Self_st : !syn_type) `(Rhs_st : !syn_type) `(PartialEq_Self_Rhs_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) )) `(PartialEq_Self_Rhs_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt)))) `(PartialOrd_Self_Rhs_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Rhs_rt) PartialEq_Self_Rhs_spec_attrs)) `(PartialOrd_Self_Rhs_spec : !(spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Rhs_rt)))) (PartialOrd_Self_Rhs_partial_cmp_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Rhs_st) →
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  syn_type_is_layoutable (((Option_els (Ordering_st)) : syn_type)) →
  PartialOrd_Self_Rhs_partial_cmp_loc ◁ᵥ{π, MetaNone} PartialOrd_Self_Rhs_partial_cmp_loc @ function_ptr [PtrSynType; PtrSynType] (<tag_type> spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), fn_spec_add_late_pre ((PartialOrd_partial_cmp_spec (RRGS:=RRGS) (PartialOrd_Self_Rhs_spec <INST!>))   <LFT> late_lft_0 <LFT> late_lft_1 <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Rhs_rt Rhs_st Rhs_ty)))%I) -∗
  typed_function π (PartialOrd_gt_def PartialOrd_Self_Rhs_partial_cmp_loc  Self_st  Rhs_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; Rhs_ty]) : ([Self_rt; Rhs_rt] : list RT), fn_spec_add_late_pre (PartialOrd_gt_base_spec Self_rt Rhs_rt Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs PartialOrd_Self_Rhs_spec_attrs  <TY> Self_ty <TY> Rhs_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Rhs_rt Rhs_st Rhs_ty))
  ∗ (⌜((trait_incl_of_PartialOrd_gt (Self_rt) (Rhs_rt) (Self_st) (Rhs_st) (PartialEq_Self_Rhs_spec_attrs) (PartialEq_Self_Rhs_spec) (PartialOrd_Self_Rhs_spec_attrs) (PartialOrd_Self_Rhs_spec)) <TY> Self_ty <TY> Rhs_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>)%Z⌝))).
End proof.

Ltac PartialOrd_gt_prelude :=
  unfold PartialOrd_gt_lemma;
  set (FN_NAME := FUNCTION_NAME "PartialOrd_gt");
  intros Self_rt Rhs_rt Self_st Rhs_st PartialEq_Self_Rhs_spec_attrs PartialEq_Self_Rhs_spec PartialOrd_Self_Rhs_spec_attrs PartialOrd_Self_Rhs_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let Self_ty := fresh "Self_ty" in
  let Rhs_ty := fresh "Rhs_ty" in
  let self := fresh "self" in
  let other := fresh "other" in
  start_function "PartialOrd_gt" ϝ ( [ulft_1 [ulft_2 [] ] ] ) ( [Self_ty [Rhs_ty [] ] ] ) ( [  self other ] ) (  self other );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "Rhs" :=
  existT _ (Rhs_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
