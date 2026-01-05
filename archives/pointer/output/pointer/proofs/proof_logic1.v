From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.pointer.generated Require Import generated_code_pointer generated_specs_pointer.
From refinedrust.examples.pointer.generated Require Import generated_template_logic1.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma logic1_proof (π : thread_id) :
  logic1_lemma π.
Proof.
  logic1_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.