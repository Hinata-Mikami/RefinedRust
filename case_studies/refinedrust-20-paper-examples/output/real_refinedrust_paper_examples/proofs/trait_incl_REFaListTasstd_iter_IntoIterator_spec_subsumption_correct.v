From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.real_refinedrust_paper_examples.generated Require Import generated_specs_real_refinedrust_paper_examples.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma REFaListTasstd_iter_IntoIterator_spec_subsumption_correct  : (REFaListTasstd_iter_IntoIterator_spec_subsumption).
Proof.
  unfold REFaListTasstd_iter_IntoIterator_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
