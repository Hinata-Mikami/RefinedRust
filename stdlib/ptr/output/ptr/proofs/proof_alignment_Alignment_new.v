From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_alignment_Alignment_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma alignment_Alignment_new_proof (π : thread_id) :
  alignment_Alignment_new_lemma π.
Proof.
  alignment_Alignment_new_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
