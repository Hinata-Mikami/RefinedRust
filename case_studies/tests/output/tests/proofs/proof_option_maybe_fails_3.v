From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_option_maybe_fails_3.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma option_maybe_fails_3_proof (π : thread_id) :
  option_maybe_fails_3_lemma π.
Proof.
  option_maybe_fails_3_prelude.

  rep liRStep; liShow.
  liInst Hevar_x0 (option_Error_MyError (F := RT_xt)).
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
