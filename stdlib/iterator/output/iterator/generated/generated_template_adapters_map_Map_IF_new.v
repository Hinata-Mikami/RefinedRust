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
Definition adapters_map_Map_IF_new_lemma (π : thread_id) : Prop :=
  ∀ `(I_rt : !RT) `(F_rt : !RT) `(I_st : !syn_type) `(F_st : !syn_type) `(DropGlue_I_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (I_rt) )) `(DropGlue_I_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (I_rt)))) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_F_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) , 
  syn_type_is_layoutable (I_st) →
  syn_type_is_layoutable (F_st) →
  syn_type_is_layoutable (((adapters_map_Map_sls (I_st) (F_st)) : syn_type)) →
  ⊢ typed_function π (adapters_map_Map_IF_new_def I_st  F_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[I_ty; F_ty]) : ([I_rt; F_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_map_Map_IF_new I_rt F_rt I_st F_st DropGlue_I_spec_attrs DropGlue_F_spec_attrs -[] -[I_ty; F_ty]) (λ π, ((typaram_wf I_rt I_st I_ty)
  ∗ (typaram_wf F_rt F_st F_ty))
  ∗ (⌜((trait_incl_of_adapters_map_Map_IF_new (I_rt) (F_rt) (I_st) (F_st) (DropGlue_I_spec_attrs) (DropGlue_I_spec) (DropGlue_F_spec_attrs) (DropGlue_F_spec))-[] -[I_ty; F_ty])%Z⌝))).
End proof.

Ltac adapters_map_Map_IF_new_prelude :=
  unfold adapters_map_Map_IF_new_lemma;
  set (FN_NAME := FUNCTION_NAME "adapters_map_Map_IF_new");
  intros I_rt F_rt I_st F_st DropGlue_I_spec_attrs DropGlue_I_spec DropGlue_F_spec_attrs DropGlue_F_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let I_ty := fresh "I_ty" in
  let F_ty := fresh "F_ty" in
  let iter := fresh "iter" in
  let f := fresh "f" in
  start_function "adapters_map_Map_IF_new" ϝ fid ( [] ) ( [I_ty [F_ty [] ] ] ) ( [  iter f ] ) ( iter f );
  intros arg_iter arg_f;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "I" :=
  existT _ (I_ty)
      ]>%E $ <[
      "F" :=
  existT _ (F_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
