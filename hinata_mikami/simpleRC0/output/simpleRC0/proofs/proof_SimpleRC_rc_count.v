From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.simpleRC0.generated Require Import generated_code_simpleRC0 generated_specs_simpleRC0 generated_template_SimpleRC_rc_count.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma SimpleRC_rc_count_proof (π : thread_id) :
  SimpleRC_rc_count_lemma π.
Proof.
  SimpleRC_rc_count_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
