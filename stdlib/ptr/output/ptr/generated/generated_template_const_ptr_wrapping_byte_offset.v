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
Definition const_ptr_wrapping_byte_offset_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (const_ptr_cast_T_u8_loc : loc) (const_ptr_cast_u8_T_loc : loc) (const_ptr_wrapping_offset_u8_loc : loc) (const_ptr_cast_T_u8_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (const_ptr_cast_u8_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (const_ptr_wrapping_offset_u8_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  const_ptr_cast_T_u8_loc ◁ᵥ{π, MetaNone} const_ptr_cast_T_u8_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_const_ptr_cast (RRGS:=RRGS) ((T_rt)) (Z) (T_st) ((IntSynType U8)) DropGlue_T_spec_attrs (drop_glue_trivial_spec_attrs (Z)) -[] -[T_ty; (int U8)]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (const_ptr_cast_T_u8_loc_linking -[] -[T_ty] π)))%I) -∗
  const_ptr_cast_u8_T_loc ◁ᵥ{π, MetaNone} const_ptr_cast_u8_T_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_const_ptr_cast (RRGS:=RRGS) (Z) ((T_rt)) ((IntSynType U8)) (T_st) (drop_glue_trivial_spec_attrs (Z)) DropGlue_T_spec_attrs -[] -[(int U8); T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (const_ptr_cast_u8_T_loc_linking -[] -[T_ty] π)))%I) -∗
  const_ptr_wrapping_offset_u8_loc ◁ᵥ{π, MetaNone} const_ptr_wrapping_offset_u8_loc @ function_ptr [PtrSynType; (IntSynType ISize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_const_ptr_wrapping_offset (RRGS:=RRGS) (Z) ((IntSynType U8)) (drop_glue_trivial_spec_attrs (Z)) -[] -[(int U8)]) (λ π, (from_assumption_hint (const_ptr_wrapping_offset_u8_loc_linking -[] -[] π)))%I) -∗
  typed_function π (const_ptr_wrapping_byte_offset_def const_ptr_cast_T_u8_loc  const_ptr_cast_u8_T_loc  const_ptr_wrapping_offset_u8_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_const_ptr_wrapping_byte_offset T_rt T_st DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_const_ptr_wrapping_byte_offset (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[] -[T_ty]) π)
  ∗ (□ (const_ptr_cast_T_u8_loc_linking -[] -[T_ty] π))
  ∗ (□ (const_ptr_cast_u8_T_loc_linking -[] -[T_ty] π))
  ∗ (□ (const_ptr_wrapping_offset_u8_loc_linking -[] -[] π)))).
End proof.

Ltac const_ptr_wrapping_byte_offset_prelude :=
  unfold const_ptr_wrapping_byte_offset_lemma;
  set (FN_NAME := FUNCTION_NAME "const_ptr_wrapping_byte_offset");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let l := fresh "l" in
  let count := fresh "count" in
  start_function "const_ptr_wrapping_byte_offset" ϝ fid ( [] ) ( [T_ty [] ] ) ( [  l count ] ) ( l count );
  intros arg_l arg_count;
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
