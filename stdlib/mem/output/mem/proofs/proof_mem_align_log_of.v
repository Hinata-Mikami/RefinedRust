From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.mem.mem.generated Require Import generated_code_mem generated_specs_mem generated_template_mem_align_log_of.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma mem_align_log_of_proof (π : thread_id) :
  mem_align_log_of_lemma π.
Proof.
  mem_align_log_of_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  apply ly_align_log_in_usize. sidecond_hook.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
