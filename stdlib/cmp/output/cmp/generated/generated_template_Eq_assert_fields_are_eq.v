From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Eq_assert_fields_are_eq_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Self_st : !syn_type) `(PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) `(PartialEq_Self_Self_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) `(Eq_Self_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(Eq_Self_spec : !(spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) , 
  syn_type_is_layoutable (Self_st) →
  ⊢ typed_function π (Eq_assert_fields_are_eq_def Self_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (Eq_assert_fields_are_eq_base_spec Self_rt Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs -[ulft_1] -[Self_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty))
  ∗ (⌜((trait_incl_of_Eq_assert_fields_are_eq (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (PartialEq_Self_Self_spec) (Eq_Self_spec_attrs) (Eq_Self_spec) (DropGlue_Self_spec))-[ulft_1] -[Self_ty])%Z⌝))).
End proof.

Ltac Eq_assert_fields_are_eq_prelude :=
  unfold Eq_assert_fields_are_eq_lemma;
  set (FN_NAME := FUNCTION_NAME "Eq_assert_fields_are_eq");
  intros Self_rt Self_st PartialEq_Self_Self_spec_attrs PartialEq_Self_Self_spec Eq_Self_spec_attrs Eq_Self_spec DropGlue_Self_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let Self_ty := fresh "Self_ty" in
  let self := fresh "self" in
  start_function "Eq_assert_fields_are_eq" ϝ ( [ulft_1 [] ] ) ( [Self_ty [] ] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
