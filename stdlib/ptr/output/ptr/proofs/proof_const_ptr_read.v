From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_read.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_read_proof (π : thread_id) :
  const_ptr_read_lemma π.
Proof.
  const_ptr_read_prelude.

  rep liRStep; liShow.
  simp_ltypes.
  rep liRStep.
  rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
  rep liRStep.
  try rewrite -Hst_eq.
  rep liRStep.
  try rewrite -Hst_eq.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rewrite -Hst_eq.
  all: try sidecond_hook.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
