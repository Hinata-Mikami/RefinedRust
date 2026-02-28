From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst2.generated Require Import generated_code_tst2 generated_specs_tst2 generated_template_id_data.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma id_data_proof (π : thread_id) :
  id_data_lemma π.
Proof.
  id_data_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
