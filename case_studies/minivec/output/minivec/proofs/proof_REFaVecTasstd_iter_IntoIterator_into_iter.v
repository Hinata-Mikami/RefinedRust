From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec generated_template_REFaVecTasstd_iter_IntoIterator_into_iter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma REFaVecTasstd_iter_IntoIterator_into_iter_proof (π : thread_id) :
  REFaVecTasstd_iter_IntoIterator_into_iter_lemma π.
Proof.
  REFaVecTasstd_iter_IntoIterator_into_iter_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
