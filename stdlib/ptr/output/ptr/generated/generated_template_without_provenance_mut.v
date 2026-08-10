From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.theories Require Export alignment shims specs.
From rrstd.ptr.ptr Require Export generated_code_ptr generated_specs_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition without_provenance_mut_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) , 
  syn_type_is_layoutable (T_st) →
  ⊢ typed_function π (ptr_without_provenance T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_without_provenance_mut T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (⌜((trait_incl_of_without_provenance_mut (T_rt) (T_st) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).
End proof.

Ltac without_provenance_mut_prelude :=
  unfold without_provenance_mut_lemma;
  set (FN_NAME := FUNCTION_NAME "without_provenance_mut");
  intros T_rt T_st DropGlue_T_spec;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let T_ty := fresh "T_ty" in
  let addr := fresh "addr" in
  start_function "without_provenance_mut" ϝ ( [] ) ( [T_ty [] ] ) (  addr ) ( addr );
  intros arg_addr;
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
