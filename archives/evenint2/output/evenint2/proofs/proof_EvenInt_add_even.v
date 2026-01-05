From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint2.generated Require Import generated_code_evenint2 generated_specs_evenint2.
From refinedrust.examples.evenint2.generated Require Import generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { apply Zeven_plus_Zeven; solve_goal. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.