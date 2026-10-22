From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy generated_template_REFTasIter_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma REFTasIter_next_proof (π : thread_id) :
  REFTasIter_next_lemma π.
Proof.
  REFTasIter_next_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
