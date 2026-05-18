From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.theories Require Export result.
From rrstd.result.result Require Export generated_code_result generated_specs_result.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Result_TE_map_err_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(E_rt : !RT) `(F_rt : !RT) `(O_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(F_st : !syn_type) `(O_st : !syn_type) `(FnOnce_O_E_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (O_rt) (((tuple1_rt) ((E_rt)))) (F_rt) )) `(FnOnce_O_E_spec : !(spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (O_rt) (((tuple1_rt) ((E_rt)))) (F_rt)))) (FnOnce_O_E_call_once_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (E_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (O_st) →
  syn_type_is_layoutable (((Result_els (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_els (T_st) (F_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (E_st)) : syn_type)) →
  FnOnce_O_E_call_once_loc ◁ᵥ{π, MetaNone} FnOnce_O_E_call_once_loc @ function_ptr [O_st; ((tuple1_sls (E_st)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((FnOnce_call_once_spec (RRGS:=RRGS) (FnOnce_O_E_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (Result_TE_map_err_def FnOnce_O_E_call_once_loc  T_st  E_st  F_st  O_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty; O_ty]) : ([T_rt; E_rt; F_rt; O_rt] : list RT), fn_spec_add_late_pre (type_of_Result_TE_map_err T_rt E_rt F_rt O_rt T_st E_st F_st O_st FnOnce_O_E_spec_attrs -[] -[T_ty; E_ty; F_ty; O_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf E_rt E_st E_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf O_rt O_st O_ty))
  ∗ (⌜((trait_incl_of_Result_TE_map_err (T_rt) (E_rt) (F_rt) (O_rt) (T_st) (E_st) (F_st) (O_st) (FnOnce_O_E_spec_attrs) (FnOnce_O_E_spec))-[] -[T_ty; E_ty; F_ty; O_ty])%Z⌝))).
End proof.

Ltac Result_TE_map_err_prelude :=
  unfold Result_TE_map_err_lemma;
  set (FN_NAME := FUNCTION_NAME "Result_TE_map_err");
  intros T_rt E_rt F_rt O_rt T_st E_st F_st O_st FnOnce_O_E_spec_attrs FnOnce_O_E_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let E_ty := fresh "E_ty" in
  let F_ty := fresh "F_ty" in
  let O_ty := fresh "O_ty" in
  let oparam := fresh "oparam" in
  let self := fresh "self" in
  let op := fresh "op" in
  start_function "Result_TE_map_err" ϝ ( [] ) ( [T_ty [E_ty [F_ty [O_ty [] ] ] ] ] ) ( [ [  oparam self ] op ] ) ( oparam self op );
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
      "F" :=
  existT _ (F_ty)
      ]>%E $ <[
      "O" :=
  existT _ (O_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
