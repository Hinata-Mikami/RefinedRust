From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.simpleRC.generated Require Import generated_code_simpleRC generated_specs_simpleRC.
From refinedrust.examples.simpleRC.generated Require Import generated_template_SimpleRC_T_new.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma SimpleRC_T_new_proof (π : thread_id) :
  SimpleRC_T_new_lemma π.
Proof.
  SimpleRC_T_new_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.