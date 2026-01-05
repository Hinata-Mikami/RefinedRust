From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.pointer2.generated Require Import generated_code_pointer2 generated_specs_pointer2.
From refinedrust.examples.pointer2.generated Require Import generated_template_logic_struct.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma logic_struct_proof (π : thread_id) :
  logic_struct_lemma π.
Proof.
  logic_struct_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.