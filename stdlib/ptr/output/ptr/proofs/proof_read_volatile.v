From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_read_volatile.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma read_volatile_proof (π : thread_id) :
  read_volatile_lemma π.
Proof.
  read_volatile_prelude.

  rep liRStep.
  simp_ltypes.
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
  all: sidecond_hook.
  all: repeat match goal with H : use_layout_alg _ = _ |- _ => try rewrite Hst_eq in H end; simplify_eq; try done.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
