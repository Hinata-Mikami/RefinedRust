From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.container_tst.generated Require Import generated_code_container_tst generated_specs_container_tst generated_template_All_Cells_read_next_value.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma All_Cells_read_next_value_proof (π : thread_id) :
  All_Cells_read_next_value_lemma π.
Proof.
  All_Cells_read_next_value_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
