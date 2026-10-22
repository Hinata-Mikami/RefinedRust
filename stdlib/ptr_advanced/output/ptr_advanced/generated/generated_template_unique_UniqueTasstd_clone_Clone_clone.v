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
Definition unique_UniqueTasstd_clone_Clone_clone_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((unique_Unique_sls (T_st)) : syn_type)) →
  ⊢ typed_function π (unique_UniqueTasstd_clone_Clone_clone_def T_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_unique_UniqueTasstd_clone_Clone_clone T_rt T_st DropGlue_T_spec_attrs -[ulft_1] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_unique_UniqueTasstd_clone_Clone_clone (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[ulft_1] -[T_ty]) π))).
End proof.

Ltac unique_UniqueTasstd_clone_Clone_clone_prelude :=
  unfold unique_UniqueTasstd_clone_Clone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "unique_UniqueTasstd_clone_Clone_clone");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  start_function "unique_UniqueTasstd_clone_Clone_clone" ϝ fid ( [ulft_1 [] ] ) ( [T_ty [] ] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
