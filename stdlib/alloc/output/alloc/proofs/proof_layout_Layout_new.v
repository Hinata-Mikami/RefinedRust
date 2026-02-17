From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_new_proof (π : thread_id) :
  layout_Layout_new_lemma π.
Proof.
  layout_Layout_new_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { eexists. done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
