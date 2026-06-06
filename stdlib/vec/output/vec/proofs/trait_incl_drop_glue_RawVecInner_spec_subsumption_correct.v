From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.vec.generated Require Import generated_specs_vec.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_RawVecInner_spec_subsumption_correct  : (drop_glue_RawVecInner_spec_subsumption).
Proof.
  unfold drop_glue_RawVecInner_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
