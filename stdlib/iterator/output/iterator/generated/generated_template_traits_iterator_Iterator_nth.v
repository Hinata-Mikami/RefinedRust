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
Definition traits_iterator_Iterator_nth_lemma (π : thread_id) : Prop :=
  ∀ `(Self_rt : !RT) `(Item_rt : !RT) `(Self_st : !syn_type) `(Item_st : !syn_type) `(DropGlue_Self_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) `(DropGlue_Self_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) `(DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Item_rt) )) `(DropGlue_Selfastraits_iterator_Iterator_Item_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Item_rt))))) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) `(traits_iterator_Iterator_Self_realization : !(trait_spec_realization (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt))))) (Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc : loc) (drop_glue_Option_Selfastraits_iterator_Iterator_Item_loc : loc) (panic_shim_loc : loc) (traits_iterator_Iterator_Self_next_loc : loc) (Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc_linking : spec_with 1 [Item_rt] (thread_id → iProp Σ)) (panic_shim_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (Self_st) →
  syn_type_is_layoutable (Item_st) →
  syn_type_is_layoutable (((Option_els (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (Item_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc ◁ᵥ{π, MetaNone} Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[Item_ty]) : ([Item_rt] : list RT), fn_spec_add_late_pre (type_of_Option_T_is_none (RRGS:=RRGS) ((Item_rt)) (Item_st) DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs -[late_lft_0] -[Item_ty]) (λ π, ((typaram_wf Item_rt Item_st Item_ty))
  ∗ (from_assumption_hint (Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc_linking -[late_lft_0] -[Item_ty] π)))%I) -∗
  drop_glue_Option_Selfastraits_iterator_Iterator_Item_loc ◁ᵥ{π, MetaNone} drop_glue_Option_Selfastraits_iterator_Iterator_Item_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[Item_ty]) : ([Item_rt] : list RT), let realization := (drop_glue_Option_realization (Item_rt) Item_st DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization) in fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[Item_ty] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[Item_ty] π))%I) -∗
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (panic_shim_loc_linking -[] -[] π)))%I) -∗
  traits_iterator_Iterator_Self_next_loc ◁ᵥ{π, MetaNone} traits_iterator_Iterator_Self_next_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (traits_iterator_Iterator_Self_lfts_inst : prod_vec lft traits_iterator_Iterator_Self_realization.(trait_ctx_lfts)) (traits_iterator_Iterator_Self_tys_inst : plist type traits_iterator_Iterator_Self_realization.(trait_ctx_tys)), spec! ( *[late_lft_0]) : 1 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre ((traits_iterator_Iterator_next_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_realization.(trait_ctx_spec) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst -[] -[]))  -[late_lft_0] -[]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (traits_iterator_Iterator_Self_realization.(trait_ctx_wf) traits_iterator_Iterator_Self_lfts_inst traits_iterator_Iterator_Self_tys_inst π))%I)) -∗
  typed_function π (traits_iterator_Iterator_nth_def Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc  drop_glue_Option_Selfastraits_iterator_Iterator_Item_loc  panic_shim_loc  traits_iterator_Iterator_Self_next_loc  Self_st  Item_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), fn_spec_add_late_pre (traits_iterator_Iterator_nth_base_spec Self_rt Item_rt Self_st Item_st DropGlue_Self_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs -[ulft_1] -[Self_ty; Item_ty]) (λ π, ((typaram_wf Self_rt Self_st Self_ty)
  ∗ (typaram_wf Item_rt Item_st Item_ty))
  ∗ (((trait_incl_of_traits_iterator_Iterator_nth (Self_rt) (Item_rt) (Self_st) (Item_st) (DropGlue_Self_spec_attrs) (DropGlue_Self_realization) (DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs) (DropGlue_Selfastraits_iterator_Iterator_Item_realization) (traits_iterator_Iterator_Self_spec_attrs) (traits_iterator_Iterator_Self_realization))-[ulft_1] -[Self_ty; Item_ty]) π)
  ∗ ((introduce_direct ((let realization := (drop_glue_Option_realization (Item_rt) Item_st DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization) in realization.(trait_ctx_wf) -[] -[Item_ty] π))))
  ∗ (□ (∀ (late_lft_0 : lft), Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc_linking -[late_lft_0] -[Item_ty] π))
  ∗ (□ (panic_shim_loc_linking -[] -[] π)))).
End proof.

Ltac traits_iterator_Iterator_nth_prelude :=
  unfold traits_iterator_Iterator_nth_lemma;
  set (FN_NAME := FUNCTION_NAME "traits_iterator_Iterator_nth");
  intros Self_rt Item_rt Self_st Item_st DropGlue_Self_spec_attrs DropGlue_Self_realization DropGlue_Selfastraits_iterator_Iterator_Item_spec_attrs DropGlue_Selfastraits_iterator_Iterator_Item_realization traits_iterator_Iterator_Self_spec_attrs traits_iterator_Iterator_Self_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let Self_ty := fresh "Self_ty" in
  let Item_ty := fresh "Item_ty" in
  let p := fresh "p" in
  let self := fresh "self" in
  let n := fresh "n" in
  start_function "traits_iterator_Iterator_nth" ϝ fid ( [ulft_1 [] ] ) ( [Self_ty [Item_ty [] ] ] ) ( [ [  p self ] n ] ) ( p self n );
  intros arg_self arg_n;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyCons ("_bb1", (["self"; "i"], ["n"], ["__0"; "__4"; "__5"; "__6"; "__7"; "__8"; "__10"; "__11"; "__12"; "__13"; "__14"; "__15"; "__16"; "__17"; "__18"; "__19"; "__20"], wrap_inv (λ (_params: ((_ * _))) (_var_self: (place_rfnRT ((place_rfnRT (Self_rt)) * gname)%type)) (_var_i: (place_rfnRT Z)), let '(init, γ) := _params in ((∃ (seq: _) (self: _) (i: _), (⌜(_var_self = ($# self))%Z⌝)
  ∗ (⌜(_var_i = ($# i))%Z⌝)
  ∗ (⌜(self.ghost = γ)%Z⌝)
  ∗ (⌜(i ≤ n)%Z⌝)
  ∗ (⌜(length seq = Z.to_nat i)%Z⌝)
  ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)
  ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p init seq self.cur))%I) : (iProp Σ)), wrap_inv (λ (L : llctx), True%I : iProp Σ), None)) $ PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "Self" :=
  existT _ (Self_ty)
      ]>%E $ <[
      "Item" :=
  existT _ (Item_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
