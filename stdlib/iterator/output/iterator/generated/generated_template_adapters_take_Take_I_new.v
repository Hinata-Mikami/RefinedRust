From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step step_by.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition adapters_take_Take_I_new_lemma (π : thread_id) : Prop :=
  ∀ `(I_rt : !RT) `(I_st : !syn_type) `(DropGlue_I_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (I_rt)))) , 
  syn_type_is_layoutable (I_st) →
  syn_type_is_layoutable (((adapters_take_Take_sls (I_st)) : syn_type)) →
  ⊢ typed_function π (adapters_take_Take_I_new_def I_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_take_Take_I_new I_rt I_st -[] -[I_ty]) (λ π, ((typaram_wf I_rt I_st I_ty))
  ∗ (⌜((trait_incl_of_adapters_take_Take_I_new (I_rt) (I_st) (DropGlue_I_spec))-[] -[I_ty])%Z⌝))).
End proof.

Ltac adapters_take_Take_I_new_prelude :=
  unfold adapters_take_Take_I_new_lemma;
  set (FN_NAME := FUNCTION_NAME "adapters_take_Take_I_new");
  intros I_rt I_st DropGlue_I_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let I_ty := fresh "I_ty" in
  let iter := fresh "iter" in
  let n := fresh "n" in
  start_function "adapters_take_Take_I_new" ϝ fid ( [] ) ( [I_ty [] ] ) ( [  iter n ] ) ( iter n );
  intros arg_iter arg_n;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "I" :=
  existT _ (I_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
