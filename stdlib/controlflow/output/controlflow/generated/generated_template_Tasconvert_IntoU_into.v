From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.controlflow.controlflow Require Export generated_code_controlflow generated_specs_controlflow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Tasconvert_IntoU_into_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(U_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(convert_From_U_T_spec_attrs : !(convert_From_spec_attrs (RRGS:=RRGS) (U_rt) (T_rt) )) `(convert_From_U_T_spec : !(spec_with 0 [] (convert_From_spec (RRGS:=RRGS) (U_rt) (T_rt)))) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_U_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) `(DropGlue_U_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) (convert_From_U_T_from_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (U_st) →
  convert_From_U_T_from_loc ◁ᵥ{π, MetaNone} convert_From_U_T_from_loc @ function_ptr [T_st] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), fn_spec_add_late_pre ((convert_From_from_spec (RRGS:=RRGS) (convert_From_U_T_spec-[] -[]))  -[] -[]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf U_rt U_st U_ty)))%I) -∗
  typed_function π (Tasconvert_IntoU_into_def convert_From_U_T_from_loc  T_st  U_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), fn_spec_add_late_pre (type_of_Tasconvert_IntoU_into T_rt U_rt T_st U_st convert_From_U_T_spec_attrs DropGlue_T_spec_attrs DropGlue_U_spec_attrs -[] -[T_ty; U_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf U_rt U_st U_ty))
  ∗ (⌜((trait_incl_of_Tasconvert_IntoU_into (T_rt) (U_rt) (T_st) (U_st) (convert_From_U_T_spec_attrs) (convert_From_U_T_spec) (DropGlue_T_spec_attrs) (DropGlue_T_spec) (DropGlue_U_spec_attrs) (DropGlue_U_spec))-[] -[T_ty; U_ty])%Z⌝))).
End proof.

Ltac Tasconvert_IntoU_into_prelude :=
  unfold Tasconvert_IntoU_into_lemma;
  set (FN_NAME := FUNCTION_NAME "Tasconvert_IntoU_into");
  intros T_rt U_rt T_st U_st convert_From_U_T_spec_attrs convert_From_U_T_spec DropGlue_T_spec_attrs DropGlue_T_spec DropGlue_U_spec_attrs DropGlue_U_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let U_ty := fresh "U_ty" in
  start_function "Tasconvert_IntoU_into" ϝ fid ( [] ) ( [T_ty [U_ty [] ] ] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "U" :=
  existT _ (U_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
