From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.real_refinedrust_paper_examples.generated Require Import generated_code_real_refinedrust_paper_examples generated_specs_real_refinedrust_paper_examples generated_template_max_list.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma max_list_proof (π : thread_id) :
  max_list_lemma π.
Proof.
  max_list_prelude.
 
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { case_bool_decide as Heq; revert Heq; normalize_and_simpl_goal_step.
    { rewrite max_list_cmp_app. simpl. 
      rewrite max_by_r.
      { rewrite max_by_l; first done.
        rewrite correct_ord_antisym. apply Min_MIN_minimal. }
      rewrite max_by_l; first last.
      { rewrite correct_ord_antisym. apply Min_MIN_minimal. }
      apply not_ord_gt_iff. by right. }
    { rewrite max_list_cmp_app. simpl.
      rewrite max_by_l; first done.
      rewrite max_by_l; first done.
      rewrite correct_ord_antisym.
      apply Min_MIN_minimal. }
  }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
