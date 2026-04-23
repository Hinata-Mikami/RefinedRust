From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_Vec_TA_is_empty.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Vec_TA_is_empty_proof (π : thread_id) :
  Vec_TA_is_empty_lemma π.
Proof.
  Vec_TA_is_empty_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
