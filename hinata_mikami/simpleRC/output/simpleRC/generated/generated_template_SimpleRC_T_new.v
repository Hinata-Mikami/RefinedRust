From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.simpleRC Require Import generated_code_simpleRC generated_specs_simpleRC.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition SimpleRC_T_new_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) (box_into_raw_RcInnerT_loc : loc) (box_new_RcInnerT_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((RcInner_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((SimpleRC_sls (T_st)) : syn_type)) →
  box_into_raw_RcInnerT_loc ◁ᵥ{π} box_into_raw_RcInnerT_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_box_into_raw (RRGS:=RRGS) (((RcInner_inv_t_rt ((T_rt))))) ((RcInner_st (T_st)))  <TY> (RcInner_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>) (λ π, (typaram_wf T_rt T_st T_ty) ∗ ⌜trait_incl_of_box_into_raw (((RcInner_inv_t_rt ((T_rt))))) ((RcInner_st (T_st)))  <TY> (RcInner_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>⌝)%I) -∗
  box_new_RcInnerT_loc ◁ᵥ{π} box_new_RcInnerT_loc @ function_ptr [(RcInner_st (T_st))] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_box_new (RRGS:=RRGS) (((RcInner_inv_t_rt ((T_rt))))) ((RcInner_st (T_st)))  <TY> (RcInner_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>) (λ π, (typaram_wf T_rt T_st T_ty) ∗ ⌜trait_incl_of_box_new (((RcInner_inv_t_rt ((T_rt))))) ((RcInner_st (T_st)))  <TY> (RcInner_inv_t ((T_rt))   <TY> T_ty <INST!>) <INST!>⌝)%I) -∗
  typed_function π (SimpleRC_T_new_def box_into_raw_RcInnerT_loc  box_new_RcInnerT_loc  T_st  ) [(SimpleRC_st (T_st)); UnitSynType; (RcInner_st (T_st)); T_st; PtrSynType; (RcInner_st (T_st)); PtrSynType; PtrSynType; PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_SimpleRC_T_new T_rt T_st  <TY> T_ty <INST!>) (λ π, (typaram_wf T_rt T_st T_ty) ∗ ⌜(trait_incl_of_SimpleRC_T_new (T_rt) (T_st)) <TY> T_ty <INST!>⌝)).
End proof.

Ltac SimpleRC_T_new_prelude :=
  unfold SimpleRC_T_new_lemma;
  set (FN_NAME := FUNCTION_NAME "SimpleRC_T_new");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let x := fresh "x" in
  start_function "SimpleRC_T_new" ϝ ( [] ) ( [T_ty [] ] ) (  x ) (  x );
  intros arg_data local___0 local___2 local_inner local___4 local_boxed local___6 local_ptr local___8 local___9;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
