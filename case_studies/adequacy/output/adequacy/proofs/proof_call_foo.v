From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy generated_template_call_foo.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma call_foo_proof (π : thread_id) :
  call_foo_lemma π.
Proof.
  call_foo_prelude.

   1: rep <-! <3000 liRStep.
   1: rep <-! <3000 liRStep.
   all: rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
