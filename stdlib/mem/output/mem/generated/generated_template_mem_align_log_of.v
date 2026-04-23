From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.mem.theories Require Export shims.
From rrstd.mem.mem Require Export generated_code_mem generated_specs_mem.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition mem_align_log_of_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) , 
  syn_type_is_layoutable (T_st) →
  ⊢ typed_function π (mem_align_log_of T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_mem_align_log_of T_rt T_st  <TY> T_ty <INST!>) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_mem_align_log_of (T_rt) (T_st)) <TY> T_ty <INST!>)%Z⌝))).
End proof.

Ltac mem_align_log_of_prelude :=
  unfold mem_align_log_of_lemma;
  set (FN_NAME := FUNCTION_NAME "mem_align_log_of");
  intros T_rt T_st;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  start_function "mem_align_log_of" ϝ ( [] ) ( [T_ty [] ] ) ( ? ) (  );
  intros;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
