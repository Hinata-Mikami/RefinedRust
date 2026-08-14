From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_closures_closure_test3.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma closures_closure_test3_proof (π : thread_id) :
  closures_closure_test3_lemma π.
Proof.
  closures_closure_test3_prelude.

  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unsafe_unfold_common_radium_defs; solve_goal. all: shelve. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
