From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.pointer2.generated Require Import generated_code_pointer2 generated_specs_pointer2.
From refinedrust.examples.pointer2.generated Require Import generated_template_pointer_add_42.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma pointer_add_42_proof (π : thread_id) :
  pointer_add_42_lemma π.
Proof.
  pointer_add_42_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.