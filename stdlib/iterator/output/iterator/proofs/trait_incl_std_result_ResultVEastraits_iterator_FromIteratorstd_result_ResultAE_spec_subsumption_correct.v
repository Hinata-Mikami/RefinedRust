From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma std_result_ResultVEastraits_iterator_FromIteratorstd_result_ResultAE_spec_subsumption_correct  : (std_result_ResultVEastraits_iterator_FromIteratorstd_result_ResultAE_spec_subsumption).
Proof.
  unfold std_result_ResultVEastraits_iterator_FromIteratorstd_result_ResultAE_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
