From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_option_get_result.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma option_get_result_proof (π : thread_id) :
  option_get_result_lemma π.
Proof.
  option_get_result_prelude.

  repeat liRStep.

(*Unshelve. all: apply try_false || apply inhabitant || apply _.*)
  (* Point:
     - I'm lacking the stratification instance, and we should totally add that.
     - But if I move out, I won't be able to do that, and I need to handle that case.
     - (Probably we shouldn't stratify that anyways. If we move stuff out, we cannot do that.)

     Goal: we should just be able to deinit a bunch of stuff.
      - we need to be careful to not do that if we could extract useful information.

     Stratification before: get everything into shape and ensure invariants are upheld againn.

    *)
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
