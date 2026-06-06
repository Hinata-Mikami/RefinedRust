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
Definition mut_ptr_wrapping_byte_add_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (mut_ptr_cast_T_u8_loc : loc) (mut_ptr_cast_u8_T_loc : loc) (mut_ptr_wrapping_add_u8_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  mut_ptr_cast_T_u8_loc ◁ᵥ{π, MetaNone} mut_ptr_cast_T_u8_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_cast (RRGS:=RRGS) ((T_rt)) (Z) (T_st) ((IntSynType U8)) -[] -[T_ty; (int U8)]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  mut_ptr_cast_u8_T_loc ◁ᵥ{π, MetaNone} mut_ptr_cast_u8_T_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_cast (RRGS:=RRGS) (Z) ((T_rt)) ((IntSynType U8)) (T_st) -[] -[(int U8); T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  mut_ptr_wrapping_add_u8_loc ◁ᵥ{π, MetaNone} mut_ptr_wrapping_add_u8_loc @ function_ptr [PtrSynType; (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_wrapping_add (RRGS:=RRGS) (Z) ((IntSynType U8)) -[] -[(int U8)]) (λ π, (True))%I) -∗
  typed_function π (mut_ptr_wrapping_byte_add_def mut_ptr_cast_T_u8_loc  mut_ptr_cast_u8_T_loc  mut_ptr_wrapping_add_u8_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_wrapping_byte_add T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_mut_ptr_wrapping_byte_add (T_rt) (T_st) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac mut_ptr_wrapping_byte_add_prelude :=
  unfold mut_ptr_wrapping_byte_add_lemma;
  set (FN_NAME := FUNCTION_NAME "mut_ptr_wrapping_byte_add");
  intros T_rt T_st DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let l := fresh "l" in
  let count := fresh "count" in
  start_function "mut_ptr_wrapping_byte_add" ϝ ( [] ) ( [T_ty [] ] ) ( [  l count ] ) ( l count );
  intros arg_l arg_count;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
