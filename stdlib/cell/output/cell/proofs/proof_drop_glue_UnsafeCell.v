From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cell.cell.generated Require Import generated_code_cell generated_specs_cell generated_template_drop_glue_UnsafeCell.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_UnsafeCell_proof (π : thread_id) :
  drop_glue_UnsafeCell_lemma π.
Proof.
  drop_glue_UnsafeCell_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
