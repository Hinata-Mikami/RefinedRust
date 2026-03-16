From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist Require Import generated_code_linkedlist generated_specs_linkedlist.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.alloc.vec.generated Require Export generated_specs_vec.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.boxed.boxed.generated Require Export generated_specs_boxed.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.stdlib.stdlib.generated Require Export generated_specs_stdlib.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition LinkedList_alloc_lemma (π : thread_id) : Prop :=
  ∀ (Box_T_into_raw_Node_loc : loc) (Box_T_new_Node_loc : loc) (Vec_TA_push_mutNode_std_alloc_Global_loc : loc) (ptr_null_mut_Node_loc : loc) , 
  syn_type_is_layoutable (((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable (((Vec_sls (PtrSynType) ((Global_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable ((Node_sls : syn_type)) →
  syn_type_is_layoutable ((LinkedList_sls : syn_type)) →
  Box_T_into_raw_Node_loc ◁ᵥ{π, MetaNone} Box_T_into_raw_Node_loc @ function_ptr [((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Box_T_into_raw (RRGS:=RRGS) ((Node_inv_t_rt)) (Node_st)  <TY> (Node_inv_t    <INST!>) <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_Box_T_into_raw ((Node_inv_t_rt)) (Node_st)  <TY> (Node_inv_t    <INST!>) <INST!>)%Z⌝))%I) -∗
  Box_T_new_Node_loc ◁ᵥ{π, MetaNone} Box_T_new_Node_loc @ function_ptr [Node_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Box_T_new (RRGS:=RRGS) ((Node_inv_t_rt)) (Node_st)  <TY> (Node_inv_t    <INST!>) <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_Box_T_new ((Node_inv_t_rt)) (Node_st)  <TY> (Node_inv_t    <INST!>) <INST!>)%Z⌝))%I) -∗
  Vec_TA_push_mutNode_std_alloc_Global_loc ◁ᵥ{π, MetaNone} Vec_TA_push_mutNode_std_alloc_Global_loc @ function_ptr [PtrSynType; PtrSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Vec_TA_push (RRGS:=RRGS) (loc) ((((Global_rt)))) (PtrSynType) ((Global_sls : syn_type)) GlobalasAllocator_spec_attrs  <TY> alias_ptr_t <TY> (Global_ty   <INST!>) <LFT> late_lft_0 <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_Vec_TA_push (loc) ((((Global_rt)))) (PtrSynType) ((Global_sls : syn_type)) GlobalasAllocator_spec_attrs (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), GlobalasAllocator_spec   <INST!>)  <TY> alias_ptr_t <TY> (Global_ty   <INST!>) <LFT> late_lft_0 <INST!>)%Z⌝))%I) -∗
  ptr_null_mut_Node_loc ◁ᵥ{π, MetaNone} ptr_null_mut_Node_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_ptr_null_mut (RRGS:=RRGS) ((Node_inv_t_rt)) (Node_st)  <TY> (Node_inv_t    <INST!>) <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_ptr_null_mut ((Node_inv_t_rt)) (Node_st)  <TY> (Node_inv_t    <INST!>) <INST!>)%Z⌝))%I) -∗
  typed_function π (LinkedList_alloc_def Box_T_into_raw_Node_loc  Box_T_new_Node_loc  Vec_TA_push_mutNode_std_alloc_Global_loc  ptr_null_mut_Node_loc  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_LinkedList_alloc  <LFT> ulft_1 <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_LinkedList_alloc <LFT> ulft_1 <INST!>)%Z⌝))).
End proof.

Ltac LinkedList_alloc_prelude :=
  unfold LinkedList_alloc_lemma;
  set (FN_NAME := FUNCTION_NAME "LinkedList_alloc");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let l := fresh "l" in
  let v := fresh "v" in
  start_function "LinkedList_alloc" ϝ ( [ulft_1 [] ] ) ( [] ) ( [  l v ] ) (  l v );
  intros arg_self arg_value;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
