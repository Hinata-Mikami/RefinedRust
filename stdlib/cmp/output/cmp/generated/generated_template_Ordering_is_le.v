From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Ordering_is_le_lemma (π : thread_id) : Prop :=
  ∀ (Ordering_as_raw_loc : loc) (Ordering_as_raw_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable ((Ordering_els : syn_type)) →
  Ordering_as_raw_loc ◁ᵥ{π, MetaNone} Ordering_as_raw_loc @ function_ptr [Ordering_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Ordering_as_raw (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (Ordering_as_raw_loc_linking -[] -[] π)))%I) -∗
  typed_function π (Ordering_is_le_def Ordering_as_raw_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Ordering_is_le -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_Ordering_is_le-[] -[]) π)
  ∗ (□ (Ordering_as_raw_loc_linking -[] -[] π)))).
End proof.

Ltac Ordering_is_le_prelude :=
  unfold Ordering_is_le_lemma;
  set (FN_NAME := FUNCTION_NAME "Ordering_is_le");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let self := fresh "self" in
  start_function "Ordering_is_le" ϝ fid ( [] ) ( [] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
