From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Iastraits_iterator_IntoIterator_into_iter_lemma (π : thread_id) : Prop :=
  ∀ `(I_rt : !RT) `(traits_iterator_Iterator_I_Item_rt : !RT) `(I_st : !syn_type) `(traits_iterator_Iterator_I_Item_st : !syn_type) `(traits_iterator_Iterator_I_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt) )) `(traits_iterator_Iterator_I_spec : !(spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt)))) , 
  syn_type_is_layoutable (I_st) →
  ⊢ typed_function π (Iastraits_iterator_IntoIterator_into_iter_def I_st  traits_iterator_Iterator_I_Item_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[I_ty; traits_iterator_Iterator_I_Item_ty]) : ([I_rt; traits_iterator_Iterator_I_Item_rt] : list RT), fn_spec_add_late_pre (type_of_Iastraits_iterator_IntoIterator_into_iter I_rt traits_iterator_Iterator_I_Item_rt I_st traits_iterator_Iterator_I_Item_st traits_iterator_Iterator_I_spec_attrs -[] -[I_ty; traits_iterator_Iterator_I_Item_ty]) (λ π, ((typaram_wf I_rt I_st I_ty)
  ∗ (typaram_wf traits_iterator_Iterator_I_Item_rt traits_iterator_Iterator_I_Item_st traits_iterator_Iterator_I_Item_ty))
  ∗ (⌜((trait_incl_of_Iastraits_iterator_IntoIterator_into_iter (I_rt) (traits_iterator_Iterator_I_Item_rt) (I_st) (traits_iterator_Iterator_I_Item_st) (traits_iterator_Iterator_I_spec_attrs) (traits_iterator_Iterator_I_spec))-[] -[I_ty; traits_iterator_Iterator_I_Item_ty])%Z⌝))).
End proof.

Ltac Iastraits_iterator_IntoIterator_into_iter_prelude :=
  unfold Iastraits_iterator_IntoIterator_into_iter_lemma;
  set (FN_NAME := FUNCTION_NAME "Iastraits_iterator_IntoIterator_into_iter");
  intros I_rt traits_iterator_Iterator_I_Item_rt I_st traits_iterator_Iterator_I_Item_st traits_iterator_Iterator_I_spec_attrs traits_iterator_Iterator_I_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let I_ty := fresh "I_ty" in
  let traits_iterator_Iterator_I_Item_ty := fresh "traits_iterator_Iterator_I_Item_ty" in
  start_function "Iastraits_iterator_IntoIterator_into_iter" ϝ ( [] ) ( [I_ty [traits_iterator_Iterator_I_Item_ty [] ] ] ) ( ? ) (  );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "I" :=
  existT _ (I_ty)
      ]>%E $ <[
      "traits_iterator_Iterator_I_Item" :=
  existT _ (traits_iterator_Iterator_I_Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
