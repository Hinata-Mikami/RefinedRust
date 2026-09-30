From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Import generated_code_closures generated_specs_closures generated_template_REFmutFasFnOnceA_call_once.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma REFmutFasFnOnceA_call_once_proof (π : thread_id) :
  REFmutFasFnOnceA_call_once_lemma π.
Proof.
  REFmutFasFnOnceA_call_once_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
