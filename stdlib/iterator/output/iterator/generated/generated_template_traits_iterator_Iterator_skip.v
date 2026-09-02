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
Definition traits_iterator_Iterator_skip_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) `(DropGlue_Self_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt)))) (adapters_skip_Skip_I_new_Self_loc : loc) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (((adapters_skip_Skip_sls (Self_st)) : syn_type)) →
  adapters_skip_Skip_I_new_Self_loc ◁ᵥ{π, MetaNone} adapters_skip_Skip_I_new_Self_loc @ function_ptr [Self_st; (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), fn_spec_add_late_pre (type_of_adapters_skip_Skip_I_new (RRGS:=RRGS) ((Self_rt)) (Self_st) -[] -[Self_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)))%I) -∗
  typed_function π (traits_iterator_Iterator_skip_def adapters_skip_Skip_I_new_Self_loc  Self_st  Item_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_skip_base_spec Self_rt Item_rt Self_st Item_st traits_iterator_Iterator_Self_spec_attrs -[] -[Self_ty; Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (⌜((trait_incl_of_traits_iterator_Iterator_skip (Self_rt) (Item_rt) (Self_st) (Item_st) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_spec) (DropGlue_Self_spec) (DropGlue_Selfastraits_iterator_Iterator_Item_spec))-[] -[Self_ty; Item_ty])%Z⌝))).
End proof.

Ltac traits_iterator_Iterator_skip_prelude :=
  unfold traits_iterator_Iterator_skip_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_skip");
  intros Self_rt Item_rt Self_st Item_st traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_spec DropGlue_Self_spec DropGlue_Selfastraits_iterator_Iterator_Item_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let p := fresh "p" in
  let self := fresh "self" in
  let n := fresh "n" in
  start_function "traits_iterator_Iterator_skip" ϝ fid ( [] ) ( [Self_ty [Item_ty [] ] ] ) ( [ [  p self ] n ] ) ( p self n );
  intros arg_self arg_n;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "Item" :=
  existT _ (Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
