From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.result.result.generated Require Import generated_code_result generated_specs_result generated_template_ResultTEasstd_clone_Clone_clone.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ResultTEasstd_clone_Clone_clone_proof (π : thread_id) :
  ResultTEasstd_clone_Clone_clone_lemma π.
Proof.
  ResultTEasstd_clone_Clone_clone_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
