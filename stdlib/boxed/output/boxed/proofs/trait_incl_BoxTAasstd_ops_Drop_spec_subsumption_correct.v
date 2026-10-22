From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.boxed.boxed.generated Require Import generated_specs_boxed.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma BoxTAasstd_ops_Drop_spec_subsumption_correct  : (BoxTAasstd_ops_Drop_spec_subsumption).
Proof.
  unfold BoxTAasstd_ops_Drop_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
