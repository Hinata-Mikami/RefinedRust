From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Import generated_code_clone generated_specs_clone generated_template_Clone_clone_from.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Clone_clone_from_proof (π : thread_id) :
  Clone_clone_from_lemma π.
Proof.
  Clone_clone_from_prelude.
  generalize RR_CONFIG_DONT_FOLD_PLACES; intros ?.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
