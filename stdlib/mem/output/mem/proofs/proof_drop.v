From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.mem.mem.generated Require Import generated_code_mem generated_specs_mem generated_template_drop.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_proof (π : thread_id) :
  drop_lemma π.
Proof.
  drop_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
