From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.range.range.generated Require Import generated_code_range generated_specs_range generated_template_drop_glue_Range.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_Range_proof (π : thread_id) :
  drop_glue_Range_lemma π.
Proof.
  drop_glue_Range_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
