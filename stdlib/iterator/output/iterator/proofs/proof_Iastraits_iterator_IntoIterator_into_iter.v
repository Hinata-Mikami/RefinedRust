From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_Iastraits_iterator_IntoIterator_into_iter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Iastraits_iterator_IntoIterator_into_iter_proof (π : thread_id) :
  Iastraits_iterator_IntoIterator_into_iter_lemma π.
Proof.
  Iastraits_iterator_IntoIterator_into_iter_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
