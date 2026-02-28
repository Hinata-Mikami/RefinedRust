From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.range.range.generated Require Import generated_code_range generated_specs_range generated_template_Range_Idx_is_empty.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Range_Idx_is_empty_proof (π : thread_id) :
  Range_Idx_is_empty_lemma π.
Proof.
  Range_Idx_is_empty_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
