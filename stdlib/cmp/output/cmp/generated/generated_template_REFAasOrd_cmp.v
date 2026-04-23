From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFAasOrd_cmp_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(PartialEq_A_A_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) `(PartialEq_A_A_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (A_rt)))) `(Eq_A_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs)) `(Eq_A_spec : !(spec_with 0 [] (Eq_spec (RRGS:=RRGS) (A_rt)))) `(PartialOrd_A_A_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) `(PartialOrd_A_A_spec : !(spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (A_rt)))) `(Ord_A_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (A_rt) PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs)) `(Ord_A_spec : !(spec_with 0 [] (Ord_spec (RRGS:=RRGS) (A_rt)))) (Ord_A_cmp_loc : loc) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  Ord_A_cmp_loc ◁ᵥ{π, MetaNone} Ord_A_cmp_loc @ function_ptr [PtrSynType; PtrSynType] (<tag_type> spec! ( *[late_lft_0; late_lft_1]) : 2 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre ((Ord_cmp_spec (RRGS:=RRGS) (Ord_A_spec <INST!>))   <LFT> late_lft_0 <LFT> late_lft_1 <INST!>) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (⌜(True)%Z⌝))%I) -∗
  typed_function π (REFAasOrd_cmp_def Ord_A_cmp_loc  A_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2; ulft_3]) : 3 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_REFAasOrd_cmp A_rt A_st PartialEq_A_A_spec_attrs Eq_A_spec_attrs PartialOrd_A_A_spec_attrs Ord_A_spec_attrs  <TY> A_ty <LFT> ulft_1 <LFT> ulft_2 <LFT> ulft_3 <INST!>) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (⌜((trait_incl_of_REFAasOrd_cmp (A_rt) (A_st) (PartialEq_A_A_spec_attrs) (PartialEq_A_A_spec) (Eq_A_spec_attrs) (Eq_A_spec) (PartialOrd_A_A_spec_attrs) (PartialOrd_A_A_spec) (Ord_A_spec_attrs) (Ord_A_spec)) <TY> A_ty <LFT> ulft_1 <LFT> ulft_2 <LFT> ulft_3 <INST!>)%Z⌝))).
End proof.

Ltac REFAasOrd_cmp_prelude :=
  unfold REFAasOrd_cmp_lemma;
  set (FN_NAME := FUNCTION_NAME "REFAasOrd_cmp");
  intros A_rt A_st PartialEq_A_A_spec_attrs PartialEq_A_A_spec Eq_A_spec_attrs Eq_A_spec PartialOrd_A_A_spec_attrs PartialOrd_A_A_spec Ord_A_spec_attrs Ord_A_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let ulft_3 := fresh "ulft_3" in
  let A_ty := fresh "A_ty" in
  start_function "REFAasOrd_cmp" ϝ ( [ulft_1 [ulft_2 [ulft_3 [] ] ] ] ) ( [A_ty [] ] ) ( ? ) (  );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "ulft_3" ulft_3 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
