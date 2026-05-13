From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.vec.theories Require Export vec.
From rrstd.alloc.vec Require Export generated_code_vec generated_specs_vec.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Vec_TA_is_empty_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_spec : !(spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) (Vec_TA_len_T_A_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (((Vec_sls (T_st) (A_st)) : syn_type)) →
  Vec_TA_len_T_A_loc ◁ᵥ{π, MetaNone} Vec_TA_len_T_A_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), fn_spec_add_late_pre (type_of_Vec_TA_len (RRGS:=RRGS) ((T_rt)) ((A_rt)) (T_st) (A_st) Allocator_A_spec_attrs -[late_lft_0] -[T_ty; A_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty)))%I) -∗
  typed_function π (Vec_TA_is_empty_def Vec_TA_len_T_A_loc  T_st  A_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), fn_spec_add_late_pre (type_of_Vec_TA_is_empty T_rt A_rt T_st A_st Allocator_A_spec_attrs -[ulft_1] -[T_ty; A_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (⌜((trait_incl_of_Vec_TA_is_empty (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs) (Allocator_A_spec))-[ulft_1] -[T_ty; A_ty])%Z⌝))).
End proof.

Ltac Vec_TA_is_empty_prelude :=
  unfold Vec_TA_is_empty_lemma;
  set (FN_NAME := FUNCTION_NAME "Vec_TA_is_empty");
  intros T_rt A_rt T_st A_st Allocator_A_spec_attrs Allocator_A_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  let A_ty := fresh "A_ty" in
  let self := fresh "self" in
  start_function "Vec_TA_is_empty" ϝ ( [ulft_1 [] ] ) ( [T_ty [A_ty [] ] ] ) (  self ) (  self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
