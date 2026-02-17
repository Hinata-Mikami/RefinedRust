From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_from_size_align_unchecked.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.


Lemma layout_Layout_from_size_align_unchecked_proof (π : thread_id) :
  layout_Layout_from_size_align_unchecked_lemma π.
Proof.
  layout_Layout_from_size_align_unchecked_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { eexists _. rewrite ly_align_of_rust_layout_align; solve_goal. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
