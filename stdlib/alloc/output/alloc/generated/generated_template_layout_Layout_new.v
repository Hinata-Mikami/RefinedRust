From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.theories Require Export layout shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.alloc.alloc Require Export generated_code_alloc generated_specs_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition layout_Layout_new_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (layout_Layout_from_size_align_unchecked_loc : loc) (mem_align_of_T_loc : loc) (mem_size_of_T_loc : loc) (layout_Layout_from_size_align_unchecked_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (mem_align_of_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (mem_size_of_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  layout_Layout_from_size_align_unchecked_loc ◁ᵥ{π, MetaNone} layout_Layout_from_size_align_unchecked_loc @ function_ptr [(IntSynType USize); (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_from_size_align_unchecked (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (layout_Layout_from_size_align_unchecked_loc_linking -[] -[] π)))%I) -∗
  mem_align_of_T_loc ◁ᵥ{π, MetaNone} mem_align_of_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mem_align_of (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (mem_align_of_T_loc_linking -[] -[T_ty] π)))%I) -∗
  mem_size_of_T_loc ◁ᵥ{π, MetaNone} mem_size_of_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mem_size_of (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (mem_size_of_T_loc_linking -[] -[T_ty] π)))%I) -∗
  typed_function π (layout_Layout_new_def layout_Layout_from_size_align_unchecked_loc  mem_align_of_T_loc  mem_size_of_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_new T_rt T_st DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_layout_Layout_new (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[] -[T_ty]) π)
  ∗ (□ (layout_Layout_from_size_align_unchecked_loc_linking -[] -[] π))
  ∗ (□ (mem_align_of_T_loc_linking -[] -[T_ty] π))
  ∗ (□ (mem_size_of_T_loc_linking -[] -[T_ty] π)))).
End proof.

Ltac layout_Layout_new_prelude :=
  unfold layout_Layout_new_lemma;
  set (FN_NAME := FUNCTION_NAME "layout_Layout_new");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  start_function "layout_Layout_new" ϝ fid ( [] ) ( [T_ty [] ] ) ( ? ) ( );
  intros;
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
