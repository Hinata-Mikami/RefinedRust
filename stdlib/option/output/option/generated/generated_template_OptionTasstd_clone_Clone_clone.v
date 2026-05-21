From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition OptionTasstd_clone_Clone_clone_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(Clone_T_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) `(Clone_T_spec : !(spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt)))) (Clone_T_clone_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (T_st)) : syn_type)) →
  Clone_T_clone_loc ◁ᵥ{π, MetaNone} Clone_T_clone_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((Clone_clone_spec (RRGS:=RRGS) (Clone_T_spec-[] -[]))  -[late_lft_0] -[]) (λ π, (True))%I) -∗
  typed_function π (OptionTasstd_clone_Clone_clone_def Clone_T_clone_loc  T_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_OptionTasstd_clone_Clone_clone T_rt T_st Clone_T_spec_attrs -[ulft_1] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_OptionTasstd_clone_Clone_clone (T_rt) (T_st) (Clone_T_spec_attrs) (Clone_T_spec))-[ulft_1] -[T_ty])%Z⌝))).
End proof.

Ltac OptionTasstd_clone_Clone_clone_prelude :=
  unfold OptionTasstd_clone_Clone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "OptionTasstd_clone_Clone_clone");
  intros T_rt T_st Clone_T_spec_attrs Clone_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  start_function "OptionTasstd_clone_Clone_clone" ϝ ( [ulft_1 [] ] ) ( [T_ty [] ] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
