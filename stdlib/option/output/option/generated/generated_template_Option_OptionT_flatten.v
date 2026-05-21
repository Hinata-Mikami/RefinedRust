From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition Option_OptionT_flatten_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (((Option_els ((Option_st (T_st)))) : syn_type)) →
  syn_type_is_layoutable (((Option_els (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls ((Option_st (T_st)))) : syn_type)) →
  ⊢ typed_function π (Option_OptionT_flatten_def T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_Option_OptionT_flatten T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_Option_OptionT_flatten (T_rt) (T_st))-[] -[T_ty])%Z⌝))).
End proof.

Ltac Option_OptionT_flatten_prelude :=
  unfold Option_OptionT_flatten_lemma;
  set (FN_NAME := FUNCTION_NAME "Option_OptionT_flatten");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let self := fresh "self" in
  start_function "Option_OptionT_flatten" ϝ ( [] ) ( [T_ty [] ] ) (  self ) ( self );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
