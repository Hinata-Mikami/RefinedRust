From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.clone.clone Require Export generated_code_clone generated_specs_clone.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition mutTasClone_clone_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  ⊢ typed_function π (mutTasClone_clone_def T_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mutTasClone_clone T_rt T_st  <TY> T_ty <LFT> ulft_1 <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_mutTasClone_clone (T_rt) (T_st)) <TY> T_ty <LFT> ulft_1 <INST!>)%Z⌝))).
End proof.

Ltac mutTasClone_clone_prelude :=
  unfold mutTasClone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "mutTasClone_clone");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let T_ty := fresh "T_ty" in
  start_function "mutTasClone_clone" ϝ ( [ulft_1 [] ] ) ( [T_ty [] ] ) ( ? ) (  );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
