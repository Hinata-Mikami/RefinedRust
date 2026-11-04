From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Ord_min_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Self_st : !syn_type) `(PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) `(PartialEq_Self_Self_realization : !(trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) `(Eq_Self_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(Eq_Self_realization : !(trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Self_rt))))) `(PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) `(PartialOrd_Self_Self_realization : !(trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt))))) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(Ord_Self_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (Self_rt) PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) `(Ord_Self_realization : !(trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Self_rt))))) (min_by_Self_closuresrclibrs1578015786_loc : loc) (min_by_Self_closuresrclibrs1578015786_loc_linking : spec_with 0 [Self_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (Self_st) →
  min_by_Self_closuresrclibrs1578015786_loc ◁ᵥ{π, MetaNone} min_by_Self_closuresrclibrs1578015786_loc @ function_ptr [Self_st; Self_st; UnitSynType] (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (type_of_min_by (RRGS:=RRGS) ((Self_rt)) (unit) (Self_st) (UnitSynType) (Ord_min_closure0_FnOnce_spec_attrs ((Self_rt)) (PartialEq_Self_Self_spec_attrs) (Eq_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Ord_Self_spec_attrs) (DropGlue_Self_spec_attrs)) DropGlue_Self_spec_attrs (drop_glue_trivial_spec_attrs (unit)) -[] -[Self_ty; unit_t]) (λ π, ((typaram_wf Self_rt Self_st Self_ty))
  ∗ (from_assumption_hint (min_by_Self_closuresrclibrs1578015786_loc_linking -[] -[Self_ty] π)))%I) -∗
  typed_function π (Ord_min_def min_by_Self_closuresrclibrs1578015786_loc  Self_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (Ord_min_base_spec Self_rt Self_st PartialEq_Self_Self_spec_attrs Eq_Self_spec_attrs PartialOrd_Self_Self_spec_attrs DropGlue_Self_spec_attrs Ord_Self_spec_attrs -[] -[Self_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty))
  ∗ (((trait_incl_of_Ord_min (Self_rt) (Self_st) (PartialEq_Self_Self_spec_attrs) (PartialEq_Self_Self_realization) (Eq_Self_spec_attrs) (Eq_Self_realization) (PartialOrd_Self_Self_spec_attrs) (PartialOrd_Self_Self_realization) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (Ord_Self_spec_attrs) (Ord_Self_realization))-[] -[Self_ty]) π)
  ∗ (□ (min_by_Self_closuresrclibrs1578015786_loc_linking -[] -[Self_ty] π)))).
End proof.

Ltac Ord_min_prelude :=
  unfold Ord_min_lemma;
  set (FN_NAME := FUNCTION_NAME "Ord_min");
  intros Self_rt Self_st PartialEq_Self_Self_spec_attrs PartialEq_Self_Self_realization Eq_Self_spec_attrs Eq_Self_realization PartialOrd_Self_Self_spec_attrs PartialOrd_Self_Self_realization DropGlue_Self_spec_attrs DropGlue_Self_realization Ord_Self_spec_attrs Ord_Self_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let Self_ty := fresh "Self_ty" in
  let self := fresh "self" in
  let other := fresh "other" in
  start_function "Ord_min" ϝ fid ( [] ) ( [Self_ty [] ] ) ( [  self other ] ) ( self other );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
