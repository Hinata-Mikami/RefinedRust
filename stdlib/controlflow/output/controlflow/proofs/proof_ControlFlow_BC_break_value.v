From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.controlflow.controlflow.generated Require Import generated_code_controlflow generated_specs_controlflow generated_template_ControlFlow_BC_break_value.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ControlFlow_BC_break_value_proof (π : thread_id) :
  ControlFlow_BC_break_value_lemma π.
Proof.
  ControlFlow_BC_break_value_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
