From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.controlflow.controlflow Require Export generated_code_controlflow generated_specs_controlflow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition ControlFlow_BC_break_value_lemma (π : thread_id) : Prop :=
  ∀ `(B_rt : !RT) `(C_rt : !RT) `(B_st : !syn_type) `(C_st : !syn_type) `(DropGlue_B_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (B_rt) )) `(DropGlue_B_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) `(DropGlue_C_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (C_rt) )) `(DropGlue_C_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (C_rt)))) (drop_glue_ControlFlow_B_C_loc : loc) , 
  syn_type_is_layoutable (B_st) →
  syn_type_is_layoutable (C_st) →
  syn_type_is_layoutable (((ControlFlow_els (B_st) (C_st)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Break_sls (B_st) (C_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (B_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (B_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (B_st)) : syn_type)) →
  drop_glue_ControlFlow_B_C_loc ◁ᵥ{π, MetaNone} drop_glue_ControlFlow_B_C_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_ControlFlow (RRGS:=RRGS) ((B_rt)) ((C_rt)) (B_st) (C_st) DropGlue_B_spec_attrs DropGlue_C_spec_attrs -[] -[B_ty; C_ty]) (λ π, ((typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf C_rt C_st C_ty)))%I) -∗
  typed_function π (ControlFlow_BC_break_value_def drop_glue_ControlFlow_B_C_loc  B_st  C_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), fn_spec_add_late_pre (type_of_ControlFlow_BC_break_value B_rt C_rt B_st C_st DropGlue_B_spec_attrs DropGlue_C_spec_attrs -[] -[B_ty; C_ty]) (λ π, ((typaram_wf B_rt B_st B_ty)
  ∗ (typaram_wf C_rt C_st C_ty))
  ∗ (⌜((trait_incl_of_ControlFlow_BC_break_value (B_rt) (C_rt) (B_st) (C_st) (DropGlue_B_spec_attrs) (DropGlue_B_spec) (DropGlue_C_spec_attrs) (DropGlue_C_spec))-[] -[B_ty; C_ty])%Z⌝))).
End proof.

Ltac ControlFlow_BC_break_value_prelude :=
  unfold ControlFlow_BC_break_value_lemma;
  set (FN_NAME := FUNCTION_NAME "ControlFlow_BC_break_value");
  intros B_rt C_rt B_st C_st DropGlue_B_spec_attrs DropGlue_B_spec DropGlue_C_spec_attrs DropGlue_C_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let B_ty := fresh "B_ty" in
  let C_ty := fresh "C_ty" in
  let self := fresh "self" in
  start_function "ControlFlow_BC_break_value" ϝ fid ( [] ) ( [B_ty [C_ty [] ] ] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "B" :=
  existT _ (B_ty)
      ]>%E $ <[
      "C" :=
  existT _ (C_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
