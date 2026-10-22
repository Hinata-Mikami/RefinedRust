From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_specs_minivec.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma REFaVecTasstd_iter_IntoIterator_spec_subsumption_correct  : (REFaVecTasstd_iter_IntoIterator_spec_subsumption).
Proof.
  unfold REFaVecTasstd_iter_IntoIterator_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
