From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_from_size_align.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_from_size_align_proof (π : thread_id) :
  layout_Layout_from_size_align_lemma π.
Proof.
  layout_Layout_from_size_align_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
