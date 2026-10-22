From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops Require Export generated_code_arithops generated_specs_arithops.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u64asSubREFau64_sub_lemma (π : thread_id) : Prop :=
  ∀ (panic_shim_loc : loc) (panic_shim_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) →
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (panic_shim_loc_linking -[] -[] π)))%I) -∗
  typed_function π (u64asSubREFau64_sub_def panic_shim_loc  ) (<tag_type> spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u64asSubREFau64_sub -[ulft_a] -[]) (λ π, (True)
  ∗ ((trait_incl_of_u64asSubREFau64_sub-[ulft_a] -[]) π)
  ∗ (□ (panic_shim_loc_linking -[] -[] π)))).
End proof.

Ltac u64asSubREFau64_sub_prelude :=
  unfold u64asSubREFau64_sub_lemma;
  set (FN_NAME := FUNCTION_NAME "u64asSubREFau64_sub");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_a := fresh "ulft_a" in
  start_function "u64asSubREFau64_sub" ϝ fid ( [ulft_a [] ] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_a", ulft_a) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
