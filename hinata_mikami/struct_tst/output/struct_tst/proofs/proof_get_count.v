From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.struct_tst.generated Require Import generated_code_struct_tst generated_specs_struct_tst generated_template_get_count.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma get_count_proof (π : thread_id) :
  get_count_lemma π.
Proof.
  get_count_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
