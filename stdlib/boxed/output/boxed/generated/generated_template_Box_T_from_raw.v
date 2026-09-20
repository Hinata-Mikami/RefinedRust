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
Definition Box_T_from_raw_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (Box_TA_from_raw_in_T_std_alloc_Global_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable (((Box_sls (T_st) ((Global_sls : syn_type))) : syn_type)) →
  Box_TA_from_raw_in_T_std_alloc_Global_loc ◁ᵥ{π, MetaNone} Box_TA_from_raw_in_T_std_alloc_Global_loc @ function_ptr [PtrSynType; (Global_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Box_TA_from_raw_in (RRGS:=RRGS) ((T_rt)) ((((Global_inv_t_rt)))) (T_st) ((Global_sls : syn_type)) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_inv_t  -[] -[])]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (Box_T_from_raw_def Box_TA_from_raw_in_T_std_alloc_Global_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Box_T_from_raw T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_Box_T_from_raw (T_rt) (T_st) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac Box_T_from_raw_prelude :=
  unfold Box_T_from_raw_lemma;
  set (FN_NAME := FUNCTION_NAME "Box_T_from_raw");
  intros T_rt T_st DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let b := fresh "b" in
  let raw := fresh "raw" in
  start_function "Box_T_from_raw" ϝ fid ( [] ) ( [T_ty [] ] ) ( [  b raw ] ) ( b raw );
  intros arg_raw;
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
