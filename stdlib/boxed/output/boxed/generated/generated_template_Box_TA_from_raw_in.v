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
Definition Box_TA_from_raw_in_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_A_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt)))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_spec : !(spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) (DropGlue_A_drop_glue_loc : loc) (unique_Unique_T_new_unchecked_T_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (((Box_sls (T_st) (A_st)) : syn_type)) →
  syn_type_is_layoutable (((unique_Unique_sls (T_st)) : syn_type)) →
  DropGlue_A_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_A_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_A_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  unique_Unique_T_new_unchecked_T_loc ◁ᵥ{π, MetaNone} unique_Unique_T_new_unchecked_T_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_unique_Unique_T_new_unchecked (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (Box_TA_from_raw_in_def DropGlue_A_drop_glue_loc  unique_Unique_T_new_unchecked_T_loc  T_st  A_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), fn_spec_add_late_pre (type_of_Box_TA_from_raw_in T_rt A_rt T_st A_st Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (⌜((trait_incl_of_Box_TA_from_raw_in (T_rt) (A_rt) (T_st) (A_st) (DropGlue_T_spec) (DropGlue_A_spec) (Allocator_A_spec_attrs) (Allocator_A_spec))-[] -[T_ty; A_ty])%Z⌝))).
End proof.

Ltac Box_TA_from_raw_in_prelude :=
  unfold Box_TA_from_raw_in_lemma;
  set (FN_NAME := FUNCTION_NAME "Box_TA_from_raw_in");
  intros T_rt A_rt T_st A_st DropGlue_T_spec DropGlue_A_spec Allocator_A_spec_attrs Allocator_A_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let A_ty := fresh "A_ty" in
  let b := fresh "b" in
  let raw := fresh "raw" in
  let alloc := fresh "alloc" in
  start_function "Box_TA_from_raw_in" ϝ ( [] ) ( [T_ty [A_ty [] ] ] ) ( [ [  b raw ] alloc ] ) ( b raw alloc );
  intros arg_raw arg_alloc;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
