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
Definition mut_ptr_cast_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(U_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_U_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) `(DropGlue_U_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt))))) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (U_st) →
  ⊢ typed_function π (mut_ptr_cast_def T_st  U_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), fn_spec_add_late_pre (type_of_mut_ptr_cast T_rt U_rt T_st U_st DropGlue_T_spec_attrs DropGlue_U_spec_attrs -[] -[T_ty; U_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf U_rt U_st U_ty))
  ∗ (((trait_incl_of_mut_ptr_cast (T_rt) (U_rt) (T_st) (U_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (DropGlue_U_spec_attrs) (DropGlue_U_realization))-[] -[T_ty; U_ty]) π))).
End proof.

Ltac mut_ptr_cast_prelude :=
  unfold mut_ptr_cast_lemma;
  set (FN_NAME := FUNCTION_NAME "mut_ptr_cast");
  intros T_rt U_rt T_st U_st DropGlue_T_spec_attrs DropGlue_T_realization DropGlue_U_spec_attrs DropGlue_U_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let U_ty := fresh "U_ty" in
  let x := fresh "x" in
  start_function "mut_ptr_cast" ϝ fid ( [] ) ( [T_ty [U_ty [] ] ] ) (  x ) ( x );
  intros arg_x;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "U" :=
  existT _ (U_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
