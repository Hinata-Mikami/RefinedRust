From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.theories Require Export alignment shims specs.
From rrstd.ptr.ptr Require Export generated_code_ptr generated_specs_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition dangling_mut_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) (mem_align_of_T_loc : loc) (without_provenance_mut_T_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  mem_align_of_T_loc ◁ᵥ{π, MetaNone} mem_align_of_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mem_align_of (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  without_provenance_mut_T_loc ◁ᵥ{π, MetaNone} without_provenance_mut_T_loc @ function_ptr [(IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_without_provenance_mut (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (dangling_mut_def mem_align_of_T_loc  without_provenance_mut_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_dangling_mut T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_dangling_mut (T_rt) (T_st))-[] -[T_ty])%Z⌝))).
End proof.

Ltac dangling_mut_prelude :=
  unfold dangling_mut_lemma;
  set (FN_NAME := FUNCTION_NAME "dangling_mut");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  start_function "dangling_mut" ϝ ( [] ) ( [T_ty [] ] ) ( ? ) ( );
  intros;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
