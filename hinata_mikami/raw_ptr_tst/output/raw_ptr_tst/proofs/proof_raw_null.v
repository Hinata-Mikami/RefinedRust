From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.raw_ptr_tst.generated Require Import generated_code_raw_ptr_tst generated_specs_raw_ptr_tst generated_template_raw_null.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_null_proof (π : thread_id) :
  raw_null_lemma π.
Proof.
  raw_null_prelude.
  liRStep. liShow.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
