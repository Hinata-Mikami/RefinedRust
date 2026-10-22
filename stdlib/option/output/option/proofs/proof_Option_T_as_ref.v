From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Import generated_code_option generated_specs_option generated_template_Option_T_as_ref.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Option_T_as_ref_proof (π : thread_id) :
  Option_T_as_ref_lemma π.
Proof.
  Option_T_as_ref_prelude.

  rep <-! liRStep; liShow.

  Unshelve. all: sidecond_solver.
  all: sidecond_hammer.
Qed.
End proof.
