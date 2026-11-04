From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.spin.spin.generated Require Import generated_specs_spin.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_subsumption_correct  : (rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_subsumption).
Proof.
  unfold rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
