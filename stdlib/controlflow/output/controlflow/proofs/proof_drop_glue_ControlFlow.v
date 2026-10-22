From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.controlflow.controlflow.generated Require Import generated_code_controlflow generated_specs_controlflow generated_template_drop_glue_ControlFlow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_ControlFlow_proof (π : thread_id) :
  drop_glue_ControlFlow_lemma π.
Proof.
  drop_glue_ControlFlow_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
