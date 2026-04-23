From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Option_T_filter_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(P_rt : !RT) `(T_st : !syn_type) `(P_st : !syn_type) `(FnOnce_P_REFT_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) `(FnOnce_P_REFT_spec : !(spec_with 1 [] (FnOnce_spec (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool))) (FnOnce_P_REFT_call_once_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (P_st) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (PtrSynType)) : syn_type)) →
  FnOnce_P_REFT_call_once_loc ◁ᵥ{π, MetaNone} FnOnce_P_REFT_call_once_loc @ function_ptr [P_st; ((tuple1_sls (PtrSynType)) : syn_type)] (<tag_type> spec! ( *[_lft_for_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((FnOnce_call_once_spec (RRGS:=RRGS) (FnOnce_P_REFT_spec <LFT> _lft_for_0 <INST!>))   <INST!>) (λ π, (True)
  ∗ (⌜(True)%Z⌝))%I) -∗
  typed_function π (Option_T_filter_def FnOnce_P_REFT_call_once_loc  T_st  P_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; P_ty]) : ([T_rt; P_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_filter T_rt P_rt T_st P_st FnOnce_P_REFT_spec_attrs  <TY> T_ty <TY> P_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf P_rt P_st P_ty))
  ∗ (⌜((trait_incl_of_Option_T_filter (T_rt) (P_rt) (T_st) (P_st) (FnOnce_P_REFT_spec_attrs) (FnOnce_P_REFT_spec)) <TY> T_ty <TY> P_ty <INST!>)%Z⌝))).
End proof.

Ltac Option_T_filter_prelude :=
  unfold Option_T_filter_lemma;
  set (FN_NAME := FUNCTION_NAME "Option_T_filter");
  intros T_rt P_rt T_st P_st FnOnce_P_REFT_spec_attrs FnOnce_P_REFT_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let P_ty := fresh "P_ty" in
  let op := fresh "op" in
  let self := fresh "self" in
  let predicate := fresh "predicate" in
  start_function "Option_T_filter" ϝ ( [] ) ( [T_ty [P_ty [] ] ] ) ( [ [  op self ] predicate ] ) (  op self predicate );
  intros arg_self arg_predicate;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "P" :=
  existT _ (P_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
