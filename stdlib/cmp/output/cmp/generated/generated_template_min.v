From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition min_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(PartialEq_T_T_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) `(PartialEq_T_T_realization : !(trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt))))) `(Eq_T_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) `(Eq_T_realization : !(trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt))))) `(PartialOrd_T_T_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) `(PartialOrd_T_T_realization : !(trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt))))) `(Ord_T_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) `(Ord_T_realization : !(trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (Ord_T_min_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  Ord_T_min_loc ◁ᵥ{π, MetaNone} Ord_T_min_loc @ function_ptr [T_st; T_st] (<tag_type> spec_collapse_params _ _ (λ (Ord_T_lfts_inst : prod_vec lft Ord_T_realization.(trait_ctx_lfts)) (Ord_T_tys_inst : plist type Ord_T_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre ((Ord_min_spec (RRGS:=RRGS) (Ord_T_realization.(trait_ctx_spec) Ord_T_lfts_inst Ord_T_tys_inst -[] -[]))  -[] -[]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (Ord_T_realization.(trait_ctx_wf) Ord_T_lfts_inst Ord_T_tys_inst π))%I)) -∗
  typed_function π (min_def Ord_T_min_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_min T_rt T_st PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs Ord_T_spec_attrs DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_min (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (PartialEq_T_T_realization) (Eq_T_spec_attrs) (Eq_T_realization) (PartialOrd_T_T_spec_attrs) (PartialOrd_T_T_realization) (Ord_T_spec_attrs) (Ord_T_realization) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[] -[T_ty]) π))).
End proof.

Ltac min_prelude :=
  unfold min_lemma;
  set (FN_NAME := FUNCTION_NAME "min");
  intros T_rt T_st PartialEq_T_T_spec_attrs PartialEq_T_T_realization Eq_T_spec_attrs Eq_T_realization PartialOrd_T_T_spec_attrs PartialOrd_T_T_realization Ord_T_spec_attrs Ord_T_realization DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  start_function "min" ϝ fid ( [] ) ( [T_ty [] ] ) ( [  v1 v2 ] ) ( v1 v2 );
  intros arg_v1 arg_v2;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
