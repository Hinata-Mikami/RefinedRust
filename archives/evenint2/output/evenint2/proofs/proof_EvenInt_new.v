From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint2.generated Require Import generated_code_evenint2 generated_specs_evenint2.
From refinedrust.examples.evenint2.generated Require Import generated_template_EvenInt_new.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma EvenInt_new_proof (π : thread_id) :
  EvenInt_new_lemma π.
Proof.
  EvenInt_new_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.