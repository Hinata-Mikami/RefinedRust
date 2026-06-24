From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.container_tst.generated Require Import generated_code_container_tst generated_specs_container_tst generated_template_read_next_value_raw.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma read_next_value_raw_proof (π : thread_id) :
  read_next_value_raw_lemma π.
Proof.
  read_next_value_raw_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
