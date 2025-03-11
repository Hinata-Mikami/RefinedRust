From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minicell.generated Require Import generated_code_minicell generated_specs_minicell generated_template_example_test1.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma example_test1_proof (π : thread_id) :
  example_test1_lemma π.
Proof.
  example_test1_prelude.

  repeat liRStep; liShow.
  liInst Hevar Zeven.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
