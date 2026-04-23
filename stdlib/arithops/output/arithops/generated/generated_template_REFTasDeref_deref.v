From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFTasDeref_deref_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  ⊢ typed_function π (REFTasDeref_deref_def T_st  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_REFTasDeref_deref T_rt T_st  <TY> T_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_REFTasDeref_deref (T_rt) (T_st)) <TY> T_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>)%Z⌝))).
End proof.

Ltac REFTasDeref_deref_prelude :=
  unfold REFTasDeref_deref_lemma;
  set (FN_NAME := FUNCTION_NAME "REFTasDeref_deref");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let T_ty := fresh "T_ty" in
  start_function "REFTasDeref_deref" ϝ ( [ulft_1 [ulft_2 [] ] ] ) ( [T_ty [] ] ) ( ? ) (  );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
