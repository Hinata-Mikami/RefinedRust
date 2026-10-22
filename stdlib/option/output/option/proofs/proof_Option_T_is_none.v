From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Import generated_code_option generated_specs_option generated_template_Option_T_is_none.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Option_T_is_none_proof (π : thread_id) :
  Option_T_is_none_lemma π.
Proof.
  Option_T_is_none_prelude.

  rep <-! liRStep; liShow.

  Unshelve. all: sidecond_solver.
  all: destruct self; naive_solver.
Qed.
End proof.
