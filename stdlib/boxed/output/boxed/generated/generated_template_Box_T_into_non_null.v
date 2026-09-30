From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.boxed.boxed Require Export generated_code_boxed generated_specs_boxed.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Box_T_into_non_null_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (Box_T_into_raw_T_loc : loc) (nonnull_NonNull_T_new_unchecked_T_loc : loc) (Box_T_into_raw_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (nonnull_NonNull_T_new_unchecked_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable (((Box_sls (T_st) ((Global_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((nonnull_NonNull_sls (T_st)) : syn_type)) →
  Box_T_into_raw_T_loc ◁ᵥ{π, MetaNone} Box_T_into_raw_T_loc @ function_ptr [(Box_st (T_st) ((Global_sls : syn_type)))] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Box_T_into_raw (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (Box_T_into_raw_T_loc_linking -[] -[T_ty] π)))%I) -∗
  nonnull_NonNull_T_new_unchecked_T_loc ◁ᵥ{π, MetaNone} nonnull_NonNull_T_new_unchecked_T_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_new_unchecked (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (nonnull_NonNull_T_new_unchecked_T_loc_linking -[] -[T_ty] π)))%I) -∗
  typed_function π (Box_T_into_non_null_def Box_T_into_raw_T_loc  nonnull_NonNull_T_new_unchecked_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Box_T_into_non_null T_rt T_st DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_Box_T_into_non_null (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[] -[T_ty]) π)
  ∗ (□ (Box_T_into_raw_T_loc_linking -[] -[T_ty] π))
  ∗ (□ (nonnull_NonNull_T_new_unchecked_T_loc_linking -[] -[T_ty] π)))).
End proof.

Ltac Box_T_into_non_null_prelude :=
  unfold Box_T_into_non_null_lemma;
  set (FN_NAME := FUNCTION_NAME "Box_T_into_non_null");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let b := fresh "b" in
  start_function "Box_T_into_non_null" ϝ fid ( [] ) ( [T_ty [] ] ) (  b ) ( b );
  intros arg_b;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
