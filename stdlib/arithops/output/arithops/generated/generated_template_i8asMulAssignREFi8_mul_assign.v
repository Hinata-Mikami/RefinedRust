From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition i8asMulAssignREFi8_mul_assign_lemma (π : thread_id) : Prop :=
  ∀ (i8asMulAssign_mul_assign_loc : loc) , 
  i8asMulAssign_mul_assign_loc ◁ᵥ{π, MetaNone} i8asMulAssign_mul_assign_loc @ function_ptr [PtrSynType; (IntSynType I8)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i8asMulAssign_mul_assign (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (True))%I) -∗
  typed_function π (i8asMulAssignREFi8_mul_assign_def i8asMulAssign_mul_assign_loc  ) (<tag_type> spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_i8asMulAssignREFi8_mul_assign -[ulft_1; ulft_2] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_i8asMulAssignREFi8_mul_assign-[ulft_1; ulft_2] -[])%Z⌝))).
End proof.

Ltac i8asMulAssignREFi8_mul_assign_prelude :=
  unfold i8asMulAssignREFi8_mul_assign_lemma;
  set (FN_NAME := FUNCTION_NAME "i8asMulAssignREFi8_mul_assign");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  start_function "i8asMulAssignREFi8_mul_assign" ϝ ( [ulft_1 [ulft_2 [] ] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
