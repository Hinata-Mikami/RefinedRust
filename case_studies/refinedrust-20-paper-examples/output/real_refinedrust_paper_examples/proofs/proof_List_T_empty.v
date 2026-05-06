From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.real_refinedrust_paper_examples.generated Require Import generated_code_real_refinedrust_paper_examples generated_specs_real_refinedrust_paper_examples generated_template_List_T_empty.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_empty_proof (π : thread_id) :
  List_T_empty_lemma π.
Proof.
  List_T_empty_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
