From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_read_volatile.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma read_volatile_proof (π : thread_id) :
  read_volatile_lemma π.
Proof.
  read_volatile_prelude.

  rep liRStep; liShow.
  simp_ltypes.
  rep liRStep; liShow.
  all: rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
  rep liRStep; liShow.
  rewrite -Hst_eq.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rewrite -Hst_eq.
  all: try sidecond_hook.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
