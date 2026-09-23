From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.controlflow.controlflow Require Export generated_code_controlflow generated_specs_controlflow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition std_option_OptionTasFromResidual_from_residual_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((Option_els (NeverSynType)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (T_st)) : syn_type)) →
  ⊢ typed_function π (std_option_OptionTasFromResidual_from_residual_def T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_std_option_OptionTasFromResidual_from_residual T_rt T_st DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_std_option_OptionTasFromResidual_from_residual (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac std_option_OptionTasFromResidual_from_residual_prelude :=
  unfold std_option_OptionTasFromResidual_from_residual_lemma;
  set (FN_NAME := FUNCTION_NAME "std_option_OptionTasFromResidual_from_residual");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  start_function "std_option_OptionTasFromResidual_from_residual" ϝ fid ( [] ) ( [T_ty [] ] ) ( ? );
  intros arg_residual;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
