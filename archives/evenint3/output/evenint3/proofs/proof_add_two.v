From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint3.generated Require Import generated_code_evenint3 generated_specs_evenint3.
From refinedrust.examples.evenint3.generated Require Import generated_template_add_two.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma add_two_proof (π : thread_id) :
  add_two_lemma π.
Proof.
  add_two_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  apply Zeven_plus_Zeven. 
  * apply H50. 
  * unfold Zeven. apply I.  
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.