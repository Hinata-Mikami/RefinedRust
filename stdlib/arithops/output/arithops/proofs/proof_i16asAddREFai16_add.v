From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops.generated Require Import generated_code_arithops generated_specs_arithops generated_template_i16asAddREFai16_add.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma i16asAddREFai16_add_proof (π : thread_id) :
  i16asAddREFai16_add_lemma π.
Proof.
  i16asAddREFai16_add_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
