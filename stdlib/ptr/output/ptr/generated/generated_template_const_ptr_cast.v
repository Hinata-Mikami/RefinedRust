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
Definition const_ptr_cast_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(U_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (U_st) →
  ⊢ typed_function π (const_ptr_cast_def T_st  U_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), fn_spec_add_late_pre (type_of_const_ptr_cast T_rt U_rt T_st U_st  <TY> T_ty <TY> U_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf U_rt U_st U_ty))
  ∗ (⌜((trait_incl_of_const_ptr_cast (T_rt) (U_rt) (T_st) (U_st)) <TY> T_ty <TY> U_ty <INST!>)%Z⌝))).
End proof.

Ltac const_ptr_cast_prelude :=
  unfold const_ptr_cast_lemma;
  set (FN_NAME := FUNCTION_NAME "const_ptr_cast");
  intros T_rt U_rt T_st U_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let U_ty := fresh "U_ty" in
  let x := fresh "x" in
  start_function "const_ptr_cast" ϝ ( [] ) ( [T_ty [U_ty [] ] ] ) (  x ) (  x );
  intros arg_x;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "U" :=
  existT _ (U_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
