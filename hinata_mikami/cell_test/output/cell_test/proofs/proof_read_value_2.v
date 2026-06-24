From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.cell_test.generated Require Import generated_code_cell_test generated_specs_cell_test generated_template_read_value_2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma read_value_2_proof (π : thread_id) :
  read_value_2_lemma π.
Proof.
  read_value_2_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
