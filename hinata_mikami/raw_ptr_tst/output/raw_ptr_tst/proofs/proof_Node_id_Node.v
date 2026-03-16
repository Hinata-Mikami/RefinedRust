From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.raw_ptr_tst.generated Require Import generated_code_raw_ptr_tst generated_specs_raw_ptr_tst generated_template_Node_id_Node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Node_id_Node_proof (π : thread_id) :
  Node_id_Node_lemma π.
Proof.
  Node_id_Node_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
