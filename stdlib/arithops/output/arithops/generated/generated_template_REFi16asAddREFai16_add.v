From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition REFi16asAddREFai16_add_lemma (π : thread_id) : Prop :=
  ∀ (panic_shim_loc : loc) , 
  syn_type_is_layoutable (((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) →
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (True))%I) -∗
  typed_function π (REFi16asAddREFai16_add_def panic_shim_loc  ) (<tag_type> spec! ( *[ulft_a; ulft_2]) : 2 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_REFi16asAddREFai16_add -[ulft_a; ulft_2] -[]) (λ π, (True)
  ∗ (⌜(trait_incl_of_REFi16asAddREFai16_add-[ulft_a; ulft_2] -[])%Z⌝))).
End proof.

Ltac REFi16asAddREFai16_add_prelude :=
  unfold REFi16asAddREFai16_add_lemma;
  set (FN_NAME := FUNCTION_NAME "REFi16asAddREFai16_add");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let ulft_a := fresh "ulft_a" in
  let ulft_2 := fresh "ulft_2" in
  start_function "REFi16asAddREFai16_add" ϝ ( [ulft_a [ulft_2 [] ] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "ulft_a" ulft_a $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
