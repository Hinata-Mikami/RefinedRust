From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Node_set_marked.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Node_set_marked_proof (π : thread_id) :
  Node_set_marked_lemma π.
Proof.
  Node_set_marked_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
