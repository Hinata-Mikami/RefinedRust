From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst2 Require Import generated_code_tst2 generated_specs_tst2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition main_lemma (π : thread_id) : Prop :=
  ∀ (id_data_loc : loc) , 
  syn_type_is_layoutable ((Data_sls : syn_type)) →
  id_data_loc ◁ᵥ{π} id_data_loc @ function_ptr [Data_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_id_data (RRGS:=RRGS)   <INST!>) (λ π, True ∗ ⌜trait_incl_of_id_data   <INST!>⌝)%I) -∗
  typed_function π (main_def id_data_loc  ) [UnitSynType; Data_st; Data_st; Data_st] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_main  <INST!>) (λ π, True ∗ ⌜trait_incl_of_main <INST!>⌝)).
End proof.

Ltac main_prelude :=
  unfold main_lemma;
  set (FN_NAME := FUNCTION_NAME "main");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  start_function "main" ϝ ( [] ) ( [] ) ( ? ) (  );
  intros local___0 local_d local___2 local___3;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
