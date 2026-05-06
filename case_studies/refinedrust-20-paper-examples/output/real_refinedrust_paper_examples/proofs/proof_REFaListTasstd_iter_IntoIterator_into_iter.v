From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.real_refinedrust_paper_examples.generated Require Import generated_code_real_refinedrust_paper_examples generated_specs_real_refinedrust_paper_examples generated_template_REFaListTasstd_iter_IntoIterator_into_iter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma REFaListTasstd_iter_IntoIterator_into_iter_proof (π : thread_id) :
  REFaListTasstd_iter_IntoIterator_into_iter_lemma π.
Proof.
  REFaListTasstd_iter_IntoIterator_into_iter_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
