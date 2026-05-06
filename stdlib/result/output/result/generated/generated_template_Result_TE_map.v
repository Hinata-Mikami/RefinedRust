From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.theories Require Export result.
From rrstd.result.result Require Export generated_code_result generated_specs_result.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Result_TE_map_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(E_rt : !RT) `(U_rt : !RT) `(F_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(U_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_T_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) )) `(FnOnce_F_T_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt)))) (FnOnce_F_T_call_once_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (E_st) →
  syn_type_is_layoutable (U_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((Result_els (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_els (U_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (T_st)) : syn_type)) →
  FnOnce_F_T_call_once_loc ◁ᵥ{π, MetaNone} FnOnce_F_T_call_once_loc @ function_ptr [F_st; ((tuple1_sls (T_st)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((FnOnce_call_once_spec (RRGS:=RRGS) (FnOnce_F_T_spec <INST!>))   <INST!>) (λ π, (True))%I) -∗
  typed_function π (Result_TE_map_def FnOnce_F_T_call_once_loc  T_st  E_st  U_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; E_ty; U_ty; F_ty]) : ([T_rt; E_rt; U_rt; F_rt] : list RT), fn_spec_add_late_pre (type_of_Result_TE_map T_rt E_rt U_rt F_rt T_st E_st U_st F_st FnOnce_F_T_spec_attrs  <TY> T_ty <TY> E_ty <TY> U_ty <TY> F_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf E_rt E_st E_ty)
  ∗ (typaram_wf U_rt U_st U_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_Result_TE_map (T_rt) (E_rt) (U_rt) (F_rt) (T_st) (E_st) (U_st) (F_st) (FnOnce_F_T_spec_attrs) (FnOnce_F_T_spec)) <TY> T_ty <TY> E_ty <TY> U_ty <TY> F_ty <INST!>)%Z⌝))).
End proof.

Ltac Result_TE_map_prelude :=
  unfold Result_TE_map_lemma;
  set (FN_NAME := FUNCTION_NAME "Result_TE_map");
  intros T_rt E_rt U_rt F_rt T_st E_st U_st F_st FnOnce_F_T_spec_attrs FnOnce_F_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let E_ty := fresh "E_ty" in
  let U_ty := fresh "U_ty" in
  let F_ty := fresh "F_ty" in
  let oparam := fresh "oparam" in
  let self := fresh "self" in
  let op := fresh "op" in
  start_function "Result_TE_map" ϝ ( [] ) ( [T_ty [E_ty [U_ty [F_ty [] ] ] ] ] ) ( [ [  oparam self ] op ] ) (  oparam self op );
  intros arg_self arg_op;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "E" :=
  existT _ (E_ty)
      ]>%E $ <[
      "U" :=
  existT _ (U_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
