From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.pointer.generated Require Import generated_code_pointer generated_specs_pointer.
From refinedrust.examples.pointer.generated Require Import generated_template_write_pointer.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma write_pointer_proof (π : thread_id) :
  write_pointer_lemma π.
Proof.
  write_pointer_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.