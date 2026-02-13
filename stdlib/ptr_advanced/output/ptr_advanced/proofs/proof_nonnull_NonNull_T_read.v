From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr_advanced.ptr_advanced.generated Require Import generated_code_ptr_advanced generated_specs_ptr_advanced generated_template_nonnull_NonNull_T_read.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma nonnull_NonNull_T_read_proof (π : thread_id) :
  nonnull_NonNull_T_read_lemma π.
Proof.
  nonnull_NonNull_T_read_prelude.

  rep liRStep; liShow.
  simp_ltypes.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
  all: sidecond_hook.
  all: repeat match goal with H : use_layout_alg _ = _ |- _ => try rewrite Hst_eq in H end; simplify_eq; try done.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
