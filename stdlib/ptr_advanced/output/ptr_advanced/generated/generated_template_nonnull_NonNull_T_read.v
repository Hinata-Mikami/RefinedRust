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
Definition nonnull_NonNull_T_read_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (nonnull_NonNull_T_as_ptr_T_loc : loc) (read_T_loc : loc) (nonnull_NonNull_T_as_ptr_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (read_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((nonnull_NonNull_sls (T_st)) : syn_type)) →
  nonnull_NonNull_T_as_ptr_T_loc ◁ᵥ{π, MetaNone} nonnull_NonNull_T_as_ptr_T_loc @ function_ptr [(nonnull_NonNull_st (T_st))] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_as_ptr (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (nonnull_NonNull_T_as_ptr_T_loc_linking -[] -[T_ty] π)))%I) -∗
  read_T_loc ◁ᵥ{π, MetaNone} read_T_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_read (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (read_T_loc_linking -[] -[T_ty] π)))%I) -∗
  typed_function π (nonnull_NonNull_T_read_def nonnull_NonNull_T_as_ptr_T_loc  read_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_read T_rt T_st DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_nonnull_NonNull_T_read (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[] -[T_ty]) π)
  ∗ (□ (nonnull_NonNull_T_as_ptr_T_loc_linking -[] -[T_ty] π))
  ∗ (□ (read_T_loc_linking -[] -[T_ty] π)))).
End proof.

Ltac nonnull_NonNull_T_read_prelude :=
  unfold nonnull_NonNull_T_read_lemma;
  set (FN_NAME := FUNCTION_NAME "nonnull_NonNull_T_read");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let k := fresh "k" in
  let ty := fresh "ty" in
  let self := fresh "self" in
  start_function "nonnull_NonNull_T_read" ϝ fid ( [] ) ( [T_ty [] ] ) ( [ [  k ty ] self ] ) ( k ty self );
  intros arg_self;
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
