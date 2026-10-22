From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Import generated_code_option generated_specs_option generated_template_Option_T_unwrap_or.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Option_T_unwrap_or_proof (π : thread_id) :
  Option_T_unwrap_or_lemma π.
Proof.
  Option_T_unwrap_or_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
