From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From stdlib.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_mem_align_of.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma mem_align_of_proof (π : thread_id) :
  mem_align_of_lemma π.
Proof.
  mem_align_of_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  by apply ly_align_in_usize.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
