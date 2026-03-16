From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.raw_ptr_tst Require Import generated_code_raw_ptr_tst generated_specs_raw_ptr_tst.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.alloc.vec.generated Require Export generated_specs_vec.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.boxed.boxed.generated Require Export generated_specs_boxed.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.stdlib.stdlib.generated Require Export generated_specs_stdlib.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition id_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (id_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_id  <INST!>) (λ π, (True)
  ∗ (⌜(trait_incl_of_id <INST!>)%Z⌝))).
End proof.

Ltac id_prelude :=
  unfold id_lemma;
  set (FN_NAME := FUNCTION_NAME "id");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let p := fresh "p" in
  let v := fresh "v" in
  start_function "id" ϝ ( [] ) ( [] ) ( [  p v ] ) (  p v );
  intros arg_p;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
