From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_without_provenance_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma without_provenance_mut_proof (π : thread_id) :
  without_provenance_mut_lemma π.
Proof.
  without_provenance_mut_prelude.

  repeat liRStep. liShow.
  set ((ProvNone, addr) : loc) as l.
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
