From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_closures_closure_test_arg_fnmut_1.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma closures_closure_test_arg_fnmut_1_proof (π : thread_id) :
  closures_closure_test_arg_fnmut_1_lemma π.
Proof.
  closures_closure_test_arg_fnmut_1_prelude.

  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
