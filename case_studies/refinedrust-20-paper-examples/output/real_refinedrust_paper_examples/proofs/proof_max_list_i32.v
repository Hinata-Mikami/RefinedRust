From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.real_refinedrust_paper_examples.generated Require Import generated_code_real_refinedrust_paper_examples generated_specs_real_refinedrust_paper_examples generated_template_max_list_i32.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma max_list_i32_proof (π : thread_id) :
  max_list_i32_lemma π.
Proof.
  max_list_i32_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unsafe_unfold_common_caesium_defs. simpl. lia. }
  { case_bool_decide as Heq; revert Heq; normalize_and_simpl_goal_step.
    all: rewrite max_list_Z_with_def; lia. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
