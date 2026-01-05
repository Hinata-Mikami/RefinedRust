From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minicell.generated Require Import generated_code_minicell generated_specs_minicell generated_template_Cell_T_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Cell_T_new_proof (π : thread_id) :
  Cell_T_new_lemma π.
Proof.
  Cell_T_new_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
