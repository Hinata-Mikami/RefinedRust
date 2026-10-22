From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy generated_template_recurse.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma recurse_proof (π : thread_id) :
  recurse_lemma π.
Proof.
  recurse_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
