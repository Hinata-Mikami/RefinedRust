From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced Require Export generated_code_ptr_advanced generated_specs_ptr_advanced.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition nonnull_NonNullTasstd_clone_Clone_clone_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((nonnull_NonNull_sls (T_st)) : syn_type)) →
  ⊢ typed_function π (nonnull_NonNullTasstd_clone_Clone_clone_def T_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNullTasstd_clone_Clone_clone T_rt T_st -[ulft_1] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_nonnull_NonNullTasstd_clone_Clone_clone (T_rt) (T_st))-[ulft_1] -[T_ty])%Z⌝))).
End proof.

Ltac nonnull_NonNullTasstd_clone_Clone_clone_prelude :=
  unfold nonnull_NonNullTasstd_clone_Clone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "nonnull_NonNullTasstd_clone_Clone_clone");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  start_function "nonnull_NonNullTasstd_clone_Clone_clone" ϝ ( [ulft_1 [] ] ) ( [T_ty [] ] ) ( ? ) (  );
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
