From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Option_T_is_none_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (Option_T_is_some_T_loc : loc) (Option_T_is_some_T_loc_linking : spec_with 1 [T_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  Option_T_is_some_T_loc ◁ᵥ{π, MetaNone} Option_T_is_some_T_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_is_some (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[late_lft_0] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (Option_T_is_some_T_loc_linking -[late_lft_0] -[T_ty] π)))%I) -∗
  typed_function π (Option_T_is_none_def Option_T_is_some_T_loc  T_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_is_none T_rt T_st DropGlue_T_spec_attrs -[ulft_1] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_Option_T_is_none (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[ulft_1] -[T_ty]) π)
  ∗ (□ (∀ (late_lft_0 : lft), Option_T_is_some_T_loc_linking -[late_lft_0] -[T_ty] π)))).
End proof.

Ltac Option_T_is_none_prelude :=
  unfold Option_T_is_none_lemma;
  set (FN_NAME := FUNCTION_NAME "Option_T_is_none");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  let self := fresh "self" in
  start_function "Option_T_is_none" ϝ fid ( [ulft_1 [] ] ) ( [T_ty [] ] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
