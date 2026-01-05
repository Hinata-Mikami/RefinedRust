From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint_new.generated Require Import generated_code_evenint_new generated_specs_evenint_new generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { apply Zeven_plus_Zeven. *exact H9. *exact H8. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
