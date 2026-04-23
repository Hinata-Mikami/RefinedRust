From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Import generated_code_cmp generated_specs_cmp generated_template_u16asPartialOrd_lt.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u16asPartialOrd_lt_proof (π : thread_id) :
  u16asPartialOrd_lt_lemma π.
Proof.
  u16asPartialOrd_lt_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
