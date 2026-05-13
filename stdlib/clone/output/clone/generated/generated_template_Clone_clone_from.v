From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.clone.clone Require Export generated_code_clone generated_specs_clone.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Clone_clone_from_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Self_st : !syn_type) `(Clone_Self_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(Clone_Self_spec : !(spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (Clone_Self_clone_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  Clone_Self_clone_loc ◁ᵥ{π, MetaNone} Clone_Self_clone_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((Clone_clone_spec (RRGS:=RRGS) (Clone_Self_spec-[] -[]))  -[late_lft_0] -[]) (λ π, (True))%I) -∗
  typed_function π (Clone_clone_from_def Clone_Self_clone_loc  Self_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (Clone_clone_from_base_spec Self_rt Self_st Clone_Self_spec_attrs -[ulft_1; ulft_2] -[Self_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty))
  ∗ (⌜((trait_incl_of_Clone_clone_from (Self_rt) (Self_st) (Clone_Self_spec_attrs) (Clone_Self_spec))-[ulft_1; ulft_2] -[Self_ty])%Z⌝))).
End proof.

Ltac Clone_clone_from_prelude :=
  unfold Clone_clone_from_lemma;
  set (FN_NAME := FUNCTION_NAME "Clone_clone_from");
  intros Self_rt Self_st Clone_Self_spec_attrs Clone_Self_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let Self_ty := fresh "Self_ty" in
  let self := fresh "self" in
  let source := fresh "source" in
  start_function "Clone_clone_from" ϝ ( [ulft_1 [ulft_2 [] ] ] ) ( [Self_ty [] ] ) ( [  self source ] ) (  self source );
  intros arg_self arg_source;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
