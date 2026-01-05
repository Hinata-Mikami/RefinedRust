From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst.generated Require Import generated_code_tst generated_specs_tst.
From refinedrust.examples.tst.generated Require Import generated_template_returns_ten.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma returns_ten_proof (π : thread_id) :
  returns_ten_lemma π.
Proof.
  returns_ten_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.