From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_alignment_Alignment_of.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma alignment_Alignment_of_proof (π : thread_id) :
  alignment_Alignment_of_lemma π.
Proof.
  alignment_Alignment_of_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { exfalso. rename select (¬ is_power_of_two _) into Hfalse.
    apply Hfalse. eexists. done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
