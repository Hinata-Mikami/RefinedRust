From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minicell.generated Require Import generated_code_minicell generated_specs_minicell generated_template_evencell_EvenCell_into_inner.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma evencell_EvenCell_into_inner_proof (π : thread_id) :
  evencell_EvenCell_into_inner_lemma π.
Proof.
  evencell_EvenCell_into_inner_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
