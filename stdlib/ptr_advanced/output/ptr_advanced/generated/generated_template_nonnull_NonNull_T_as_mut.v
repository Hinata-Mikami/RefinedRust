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
Definition nonnull_NonNull_T_as_mut_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (nonnull_NonNull_T_as_ptr_T_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((nonnull_NonNull_sls (T_st)) : syn_type)) →
  nonnull_NonNull_T_as_ptr_T_loc ◁ᵥ{π, MetaNone} nonnull_NonNull_T_as_ptr_T_loc @ function_ptr [(nonnull_NonNull_st (T_st))] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_as_ptr (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (nonnull_NonNull_T_as_mut_def nonnull_NonNull_T_as_ptr_T_loc  T_st  ) (<tag_type> spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_as_mut T_rt T_st DropGlue_T_spec_attrs -[ulft_a; ulft_2] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_nonnull_NonNull_T_as_mut (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_spec))-[ulft_a; ulft_2] -[T_ty])%Z⌝))).
End proof.

Ltac nonnull_NonNull_T_as_mut_prelude :=
  unfold nonnull_NonNull_T_as_mut_lemma;
  set (FN_NAME := FUNCTION_NAME "nonnull_NonNull_T_as_mut");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_a := fresh "ulft_a" in
  let ulft_2 := fresh "ulft_2" in
  let T_ty := fresh "T_ty" in
  let x := fresh "x" in
  let self := fresh "self" in
  start_function "nonnull_NonNull_T_as_mut" ϝ fid ( [ulft_a [ulft_2 [] ] ] ) ( [T_ty [] ] ) ( [  x self ] ) ( x self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_a", ulft_a) :: ("ulft_2", ulft_2) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  check_unconstrained_lft "vuclft4";
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
