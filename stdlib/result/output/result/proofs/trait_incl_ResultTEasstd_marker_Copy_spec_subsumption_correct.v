From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.result.result.generated Require Import generated_specs_result.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ResultTEasstd_marker_Copy_spec_subsumption_correct  : (ResultTEasstd_marker_Copy_spec_subsumption).
Proof.
  unfold ResultTEasstd_marker_Copy_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
