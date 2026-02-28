From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint_new.generated Require Import generated_code_evenint_new generated_specs_evenint_new generated_template_main.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma main_proof (π : thread_id) :
  main_lemma π.
Proof.
  main_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  {rewrite MinInt_eq. reflexivity. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.