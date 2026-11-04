From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_specs_iterator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_subsumption_correct  : (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_subsumption).
Proof.
  unfold step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
