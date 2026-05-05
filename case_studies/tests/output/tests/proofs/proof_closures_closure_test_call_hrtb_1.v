From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_closures_closure_test_call_hrtb_1.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma closures_closure_test_call_hrtb_1_proof (π : thread_id) :
  closures_closure_test_call_hrtb_1_lemma π.
Proof.
  closures_closure_test_call_hrtb_1_prelude.

  repeat liRStep; liShow.
  iRename select (∀ _, FnOnce_Pre _ _ _ _ _)%I into "Hpre".
  iSpecialize ("Hpre" $! _).
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
