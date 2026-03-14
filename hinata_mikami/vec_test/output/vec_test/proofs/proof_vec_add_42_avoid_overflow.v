From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.vec_test.generated Require Import generated_code_vec_test generated_specs_vec_test generated_template_vec_add_42_avoid_overflow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma vec_add_42_avoid_overflow_proof (π : thread_id) :
  vec_add_42_avoid_overflow_lemma π.
Proof.
  vec_add_42_avoid_overflow_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
