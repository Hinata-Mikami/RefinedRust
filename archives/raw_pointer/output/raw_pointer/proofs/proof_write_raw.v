From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.raw_pointer.generated Require Import generated_code_raw_pointer generated_specs_raw_pointer.
From refinedrust.examples.raw_pointer.generated Require Import generated_template_write_raw.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma write_raw_proof (π : thread_id) :
  write_raw_lemma π.
Proof.
  write_raw_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.