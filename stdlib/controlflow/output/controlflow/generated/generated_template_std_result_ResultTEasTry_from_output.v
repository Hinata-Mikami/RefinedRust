From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.controlflow.controlflow Require Export generated_code_controlflow generated_specs_controlflow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition std_result_ResultTEasTry_from_output_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (E_st) →
  syn_type_is_layoutable (((Result_els (T_st) (E_st)) : syn_type)) →
  ⊢ typed_function π (std_result_ResultTEasTry_from_output_def T_st  E_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), fn_spec_add_late_pre (type_of_std_result_ResultTEasTry_from_output T_rt E_rt T_st E_st  <TY> T_ty <TY> E_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf E_rt E_st E_ty))
  ∗ (⌜((trait_incl_of_std_result_ResultTEasTry_from_output (T_rt) (E_rt) (T_st) (E_st)) <TY> T_ty <TY> E_ty <INST!>)%Z⌝))).
End proof.

Ltac std_result_ResultTEasTry_from_output_prelude :=
  unfold std_result_ResultTEasTry_from_output_lemma;
  set (FN_NAME := FUNCTION_NAME "std_result_ResultTEasTry_from_output");
  intros T_rt E_rt T_st E_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let E_ty := fresh "E_ty" in
  start_function "std_result_ResultTEasTry_from_output" ϝ ( [] ) ( [T_ty [E_ty [] ] ] ) ( ? ) (  );
  intros arg_output;
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
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
