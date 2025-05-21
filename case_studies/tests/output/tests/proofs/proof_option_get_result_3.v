From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_option_get_result_3.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma option_get_result_3_proof (π : thread_id) :
  option_get_result_3_lemma π.
Proof.
  option_get_result_3_prelude.

  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
  (* TODO debug slowdown *)

  (* TODO: debug a bit more -- it's still fairly slow. 
     maybe seal op_alg also. *)
Qed.
End proof.
