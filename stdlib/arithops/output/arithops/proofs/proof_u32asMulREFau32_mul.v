From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops.generated Require Import generated_code_arithops generated_specs_arithops generated_template_u32asMulREFau32_mul.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u32asMulREFau32_mul_proof (π : thread_id) :
  u32asMulREFau32_mul_lemma π.
Proof.
  u32asMulREFau32_mul_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
