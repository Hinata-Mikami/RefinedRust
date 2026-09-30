From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy generated_template_Oneasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Oneasstd_iter_Iterator_next_proof (π : thread_id) :
  Oneasstd_iter_Iterator_next_lemma π.
Proof.
  Oneasstd_iter_Iterator_next_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
