From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr_advanced.ptr_advanced.generated Require Import generated_code_ptr_advanced generated_specs_ptr_advanced generated_template_nonnull_NonNull_T_is_aligned_to.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma nonnull_NonNull_T_is_aligned_to_proof (π : thread_id) :
  nonnull_NonNull_T_is_aligned_to_lemma π.
Proof.
  nonnull_NonNull_T_is_aligned_to_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
