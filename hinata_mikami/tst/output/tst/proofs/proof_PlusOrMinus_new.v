From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst.generated Require Import generated_code_tst generated_specs_tst generated_template_PlusOrMinus_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma PlusOrMinus_new_proof (π : thread_id) :
  PlusOrMinus_new_lemma π.
Proof.
  PlusOrMinus_new_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
