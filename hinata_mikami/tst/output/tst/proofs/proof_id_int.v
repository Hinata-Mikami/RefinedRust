From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst.generated Require Import generated_code_tst generated_specs_tst generated_template_id_int.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma id_int_proof (π : thread_id) :
  id_int_lemma π.
Proof.
  id_int_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
