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
Definition nonnull_NonNull_T_is_aligned_to_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (mut_ptr_is_aligned_to_T_loc : loc) (nonnull_NonNull_T_as_ptr_T_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((nonnull_NonNull_sls (T_st)) : syn_type)) →
  mut_ptr_is_aligned_to_T_loc ◁ᵥ{π, MetaNone} mut_ptr_is_aligned_to_T_loc @ function_ptr [PtrSynType; (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_is_aligned_to (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  nonnull_NonNull_T_as_ptr_T_loc ◁ᵥ{π, MetaNone} nonnull_NonNull_T_as_ptr_T_loc @ function_ptr [(nonnull_NonNull_st (T_st))] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_as_ptr (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (nonnull_NonNull_T_is_aligned_to_def mut_ptr_is_aligned_to_T_loc  nonnull_NonNull_T_as_ptr_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_is_aligned_to T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_nonnull_NonNull_T_is_aligned_to (T_rt) (T_st) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac nonnull_NonNull_T_is_aligned_to_prelude :=
  unfold nonnull_NonNull_T_is_aligned_to_lemma;
  set (FN_NAME := FUNCTION_NAME "nonnull_NonNull_T_is_aligned_to");
  intros T_rt T_st DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let self := fresh "self" in
  let align := fresh "align" in
  start_function "nonnull_NonNull_T_is_aligned_to" ϝ fid ( [] ) ( [T_ty [] ] ) ( [  self align ] ) ( self align );
  intros arg_self arg_align;
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
