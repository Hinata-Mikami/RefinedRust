From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.theories Require Export result.
From rrstd.result.result Require Export generated_code_result generated_specs_result.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition drop_glue_Result_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_E_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (E_rt) )) `(DropGlue_E_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt)))) (DropGlue_E_drop_glue_loc : loc) (DropGlue_T_drop_glue_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (E_st) →
  syn_type_is_layoutable (((Result_els (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls (T_st) (E_st)) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (T_st) (E_st)) : syn_type)) →
  DropGlue_E_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_E_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_E_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (drop_glue_Result_def DropGlue_E_drop_glue_loc  DropGlue_T_drop_glue_loc  T_st  E_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_Result T_rt E_rt T_st E_st DropGlue_T_spec_attrs DropGlue_E_spec_attrs -[] -[T_ty; E_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf E_rt E_st E_ty))
  ∗ (⌜((trait_incl_of_drop_glue_Result (T_rt) (E_rt) (T_st) (E_st) (DropGlue_T_spec_attrs) (DropGlue_T_spec) (DropGlue_E_spec_attrs) (DropGlue_E_spec))-[] -[T_ty; E_ty])%Z⌝))).
End proof.

Ltac drop_glue_Result_prelude :=
  unfold drop_glue_Result_lemma;
  set (FN_NAME := FUNCTION_NAME "drop_glue_Result");
  intros T_rt E_rt T_st E_st DropGlue_T_spec_attrs DropGlue_T_spec DropGlue_E_spec_attrs DropGlue_E_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let E_ty := fresh "E_ty" in
  start_function "drop_glue_Result" ϝ fid ( [] ) ( [T_ty [E_ty [] ] ] ) ( ? );
  intros arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "E" :=
  existT _ (E_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
