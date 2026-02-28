From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_specs_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma alignment_AlignmentEnumasstd_clone_Clone_spec_subsumption_correct  : (alignment_AlignmentEnumasstd_clone_Clone_spec_subsumption).
Proof.
  unfold alignment_AlignmentEnumasstd_clone_Clone_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
