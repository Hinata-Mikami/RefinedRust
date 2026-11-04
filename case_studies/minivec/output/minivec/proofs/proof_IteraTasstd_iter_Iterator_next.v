From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec generated_template_IteraTasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma IteraTasstd_iter_Iterator_next_proof (π : thread_id) :
  IteraTasstd_iter_Iterator_next_lemma π.
Proof.
  IteraTasstd_iter_Iterator_next_prelude.

  rep <-! liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - apply drop_S. apply list_lookup_lookup_total_lt. lia.
  - apply drop_ge. lia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
