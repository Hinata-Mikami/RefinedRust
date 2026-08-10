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
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(PartialEq_T_T_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) )) `(PartialEq_T_T_spec : !(spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (T_rt) (T_rt)))) `(Eq_T_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs)) `(Eq_T_spec : !(spec_with 0 [] (Eq_spec (RRGS:=RRGS) (T_rt)))) `(PartialOrd_T_T_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (T_rt) (T_rt) PartialEq_T_T_spec_attrs)) `(PartialOrd_T_T_spec : !(spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (T_rt) (T_rt)))) `(Ord_T_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (T_rt) PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs)) `(Ord_T_spec : !(spec_with 0 [] (Ord_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (Ord_T_min_loc : loc) , 
  syn_type_is_layoutable (T_st) →
  Ord_T_min_loc ◁ᵥ{π, MetaNone} Ord_T_min_loc @ function_ptr [T_st; T_st] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre ((Ord_min_spec (RRGS:=RRGS) (Ord_T_spec-[] -[]))  -[] -[]) (λ π, ((typaram_wf T_rt T_st T_ty)))%I) -∗
  typed_function π (min_def Ord_T_min_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_min T_rt T_st PartialEq_T_T_spec_attrs Eq_T_spec_attrs PartialOrd_T_T_spec_attrs Ord_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_min (T_rt) (T_st) (PartialEq_T_T_spec_attrs) (PartialEq_T_T_spec) (Eq_T_spec_attrs) (Eq_T_spec) (PartialOrd_T_T_spec_attrs) (PartialOrd_T_T_spec) (Ord_T_spec_attrs) (Ord_T_spec) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac min_prelude :=
  unfold min_lemma;
  set (FN_NAME := FUNCTION_NAME "min");
  intros T_rt T_st PartialEq_T_T_spec_attrs PartialEq_T_T_spec Eq_T_spec_attrs Eq_T_spec PartialOrd_T_T_spec_attrs PartialOrd_T_T_spec Ord_T_spec_attrs Ord_T_spec DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  start_function "min" ϝ ( [] ) ( [T_ty [] ] ) ( [  v1 v2 ] ) ( v1 v2 );
  intros arg_v1 arg_v2;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
