From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Ord_min_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Self_st : !syn_type) `(PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) `(PartialEq_Self_Self_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) `(Eq_Self_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(Eq_Self_spec : !(spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt)))) `(PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(PartialOrd_Self_Self_spec : !(spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) `(Ord_Self_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) `(Ord_Self_spec : !(spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt)))) (min_by_Self_closuresrclibrs1558015586_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  min_by_Self_closuresrclibrs1558015586_loc ◁ᵥ{π, MetaNone} min_by_Self_closuresrclibrs1558015586_loc @ function_ptr [Self_st; Self_st; UnitSynType] (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (type_of_min_by (RRGS:=RRGS) ((Self_rt)) (unit) (Self_st) (UnitSynType) (Ord_min_closure0_FnOnce_spec_attrs ((Self_rt)) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs))  <TY> Self_ty <TY> unit_t <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty))
  ∗ (⌜(trait_incl_of_min_by ((Self_rt)) (unit) (Self_st) (UnitSynType) (Ord_min_closure0_FnOnce_spec_attrs ((Self_rt)) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs)) (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), Ord_min_closure0_FnOnce_spec (Self_rt) Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs Ord_Self_spec_attrs<TY> Self_ty<LFT> _lft_for_1 <LFT> _lft_for_0 <INST!>)  <TY> Self_ty <TY> unit_t <INST!>)%Z⌝))%I) -∗
  typed_function π (Ord_min_def min_by_Self_closuresrclibrs1558015586_loc  Self_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (Ord_min_base_spec Self_rt Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs Ord_Self_spec_attrs  <TY> Self_ty <INST!>) (λ π, ((typaram_wf Self_rt Self_st Self_ty))
  ∗ (⌜((trait_incl_of_Ord_min (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (PartialEq_Self_Self_spec) (Eq_Self_spec_attrs) (Eq_Self_spec) (PartialOrd_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec) (Ord_Self_spec_attrs) (Ord_Self_spec)) <TY> Self_ty <INST!>)%Z⌝))).
End proof.

Ltac Ord_min_prelude :=
  unfold Ord_min_lemma;
  set (FN_NAME := FUNCTION_NAME "Ord_min");
  intros Self_rt Self_st PartialEq_Self_Self_spec_attrs PartialEq_Self_Self_spec Eq_Self_spec_attrs Eq_Self_spec PartialOrd_Self_Self_spec_attrs PartialOrd_Self_Self_spec Ord_Self_spec_attrs Ord_Self_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let Self_ty := fresh "Self_ty" in
  let self := fresh "self" in
  let other := fresh "other" in
  start_function "Ord_min" ϝ ( [] ) ( [Self_ty [] ] ) ( [  self other ] ) (  self other );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
