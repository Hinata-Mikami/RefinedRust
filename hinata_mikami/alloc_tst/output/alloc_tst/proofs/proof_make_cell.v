From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.alloc_tst.generated Require Import generated_code_alloc_tst generated_specs_alloc_tst generated_template_make_cell.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma make_cell_proof (π : thread_id) :
  make_cell_lemma π.
Proof.
  make_cell_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
