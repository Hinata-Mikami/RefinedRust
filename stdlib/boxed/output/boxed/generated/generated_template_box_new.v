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
Definition box_new_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (alloc_alloc_loc : loc) (dangling_T_loc : loc) (layout_Layout_new_T_loc : loc) (mem_size_of_T_loc : loc) (mut_ptr_write_T_loc : loc) (unique_Unique_T_new_unchecked_T_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable (((Box_sls (T_st) ((Global_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((unique_Unique_sls (T_st)) : syn_type)) →
  alloc_alloc_loc ◁ᵥ{π, MetaNone} alloc_alloc_loc @ function_ptr [(layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_alloc_alloc (RRGS:=RRGS)  -[] -[]) (λ π, (True))%I) -∗
  dangling_T_loc ◁ᵥ{π, MetaNone} dangling_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_dangling (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  layout_Layout_new_T_loc ◁ᵥ{π, MetaNone} layout_Layout_new_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_new (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  mem_size_of_T_loc ◁ᵥ{π, MetaNone} mem_size_of_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mem_size_of (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  mut_ptr_write_T_loc ◁ᵥ{π, MetaNone} mut_ptr_write_T_loc @ function_ptr [PtrSynType; T_st] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_write (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  unique_Unique_T_new_unchecked_T_loc ◁ᵥ{π, MetaNone} unique_Unique_T_new_unchecked_T_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_unique_Unique_T_new_unchecked (RRGS:=RRGS) ((T_rt)) (T_st) -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (box_new_def alloc_alloc_loc  dangling_T_loc  layout_Layout_new_T_loc  mem_size_of_T_loc  mut_ptr_write_T_loc  unique_Unique_T_new_unchecked_T_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_box_new T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_box_new (T_rt) (T_st) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac box_new_prelude :=
  unfold box_new_lemma;
  set (FN_NAME := FUNCTION_NAME "box_new");
  intros T_rt T_st DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let x := fresh "x" in
  start_function "box_new" ϝ ( [] ) ( [T_ty [] ] ) (  x ) ( x );
  intros arg_x;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
