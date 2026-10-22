From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.controlflow.controlflow.generated Require Import generated_code_controlflow generated_specs_controlflow generated_template_Tasconvert_IntoU_into.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Tasconvert_IntoU_into_proof (π : thread_id) :
  Tasconvert_IntoU_into_lemma π.
Proof.
  Tasconvert_IntoU_into_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
