From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.boxed.boxed.generated Require Import generated_code_boxed generated_specs_boxed generated_template_Box_TA_from_raw_in.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Box_TA_from_raw_in_proof (π : thread_id) :
  Box_TA_from_raw_in_lemma π.
Proof.
  Box_TA_from_raw_in_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
