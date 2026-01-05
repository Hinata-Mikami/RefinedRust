From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst.generated Require Import generated_code_tst generated_specs_tst.
From refinedrust.examples.tst.generated Require Import generated_template_do_nothing.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma do_nothing_proof (π : thread_id) :
  do_nothing_lemma π.
Proof.
  do_nothing_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.