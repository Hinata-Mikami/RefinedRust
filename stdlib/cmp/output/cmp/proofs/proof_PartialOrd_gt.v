From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Import generated_code_cmp generated_specs_cmp generated_template_PartialOrd_gt.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma PartialOrd_gt_proof (π : thread_id) :
  PartialOrd_gt_lemma π.
Proof.
  PartialOrd_gt_prelude.

  repeat liRStep; liShow.
  rename select (PartialOrd_POrd _ _ _ = _) into Heq.
  rewrite Heq.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rename select (PartialOrd_POrd _ _ _ = _) into Heq.
  all: by rewrite Heq.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
